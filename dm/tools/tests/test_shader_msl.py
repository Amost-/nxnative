"""A profile's own MSL rewrites (dm/games/<id>/shader_msl.py, dmsh_build.py profile_msl): the loader takes a
profile's REWRITES and refuses malformed ones, every profile's file loads, and Ocarina of Time's HDR tone map rewrites
the shader it was written for, refuses any other source, and its curve joins the game's ACES fit without a step or a
kink and stays under the peak."""
import ast
import importlib.util
import os
from pathlib import Path
import re
import sys
import tempfile
import unittest

REPO = Path(__file__).resolve().parents[3]
TOOLS = REPO / 'dm/gfx/tools'
GAMES = REPO / 'dm/games'


def loader():
    """dmsh_build.py's profile_msl alone: importing the build itself needs a game profile and its tools."""
    tree = ast.parse((TOOLS / 'dmsh_build.py').read_text())
    nodes: list[ast.stmt] = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'profile_msl']
    ns = {'os': os, 're': re, 'sys': sys}
    exec(compile(ast.Module(body=nodes, type_ignores=[]), str(TOOLS / 'dmsh_build.py'), 'exec'), ns)
    return ns['profile_msl']


def module(path):
    spec = importlib.util.spec_from_file_location('shader_msl_under_test', path)
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
    return mod


PROFILE_MSL = loader()
OCARINA = module(GAMES / '0400486024DEC000/shader_msl.py')

# The lines of the translated shader the rewrite anchors on, in its order; the real source has the arithmetic between them.
SHADER = '''fragment main0_out main0(main0_in in [[stage_in]])
{
    main0_out out = {};
    float _151 = 1.0;
    float _155 = 1.0;
    float _167 = 1.0;
    float _223 = _221 ? 0.0 : U[4].y;
    float _319 = precise::min(_313, (16u < (N >> 2u)) ? U[4].x : 0.0);
    float _321 = precise::min(_315, (16u < (N >> 2u)) ? U[4].x : 0.0);
    float _323 = precise::min(_317, (16u < (N >> 2u)) ? U[4].x : 0.0);
    out.m_41.x = _319;
    out.m_41.y = _321;
    out.m_41.z = _323;
    out.m_41.w = _87;
    return out;
}
'''


class Loader(unittest.TestCase):
    def write(self, text):
        d = tempfile.TemporaryDirectory(); self.addCleanup(d.cleanup)
        p = Path(d.name) / 'shader_msl.py'; p.write_text(text)
        return str(p)

    def test_a_profile_without_the_file_has_no_rewrites(self):
        self.assertEqual(PROFILE_MSL(str(GAMES / 'no-such-profile/shader_msl.py')), ({}, b''))

    def test_rewrites_and_the_files_bytes(self):
        text = 'def f(msl): return msl + "x"\nREWRITES = {"0123456789abcdef": f}\n'
        rewrites, source = PROFILE_MSL(self.write(text))
        self.assertEqual(rewrites['0123456789abcdef']('a'), 'ax')
        self.assertEqual(source, text.encode())

    def test_a_malformed_key_or_value_stops_the_build(self):
        for text in ('REWRITES = {"774f": lambda m: m}\n', 'REWRITES = {"0123456789ABCDEF": lambda m: m}\n', 'REWRITES = {"0123456789abcdef": "text"}\n'):
            with self.assertRaises(SystemExit) as e: PROFILE_MSL(self.write(text))
            self.assertIn('[RED]', str(e.exception))

    def test_every_profiles_file_loads(self):
        for path in sorted(GAMES.glob('*/shader_msl.py')):
            rewrites, source = PROFILE_MSL(str(path))
            self.assertTrue(rewrites and source, path)


class OcarinaHdrToneMap(unittest.TestCase):
    def test_the_outputs_are_replaced_and_the_peak_is_the_games(self):
        out = OCARINA.REWRITES['774f2663242dbfcf'](SHADER)
        self.assertNotIn('out.m_41.x = _319;', out)
        self.assertIn('float dm_peak = (16u < (N >> 2u)) ? U[4].x : 0.0;', out)
        self.assertIn('float3 dm_out = float3(_319, _321, _323);', out)   # the game's result stays the fallback
        self.assertEqual(out.count('out.m_41.x = '), 1)
        self.assertTrue(out.endswith('    out.m_41.w = _87;\n    return out;\n}\n'))

    def test_a_uniformly_renumbered_translation_is_accepted_under_its_names(self):
        """A chain that shifts every local by the same amount and renames the output member (b-7b11287a1dc7: 7 lower, m_34)
        is the same shader: the block must read that source's names, not the first chain's."""
        import re
        moved = re.sub(r'\b_(\d+)\b', lambda m: f'_{int(m.group(1)) - 7}', SHADER).replace('out.m_41.', 'out.m_34.')
        out = OCARINA.REWRITES['774f2663242dbfcf'](moved)
        self.assertIn('float3 dm_out = float3(_312, _314, _316);', out)
        self.assertIn('float dm_thr = _216;', out)
        self.assertIn('float3(_148, _144, _160)', out)
        self.assertEqual(out.count('out.m_34.x = '), 1)
        self.assertNotIn('m_41', out)
        self.assertNotIn('_319', out)

    def test_another_source_is_refused(self):
        for other in (SHADER.replace('_223', '_225'), SHADER.replace('    out.m_41.y = _321;\n', ''), SHADER + SHADER, 'fragment main0_out main0() {}\n'):
            with self.assertRaises(ValueError): OCARINA.hdr_tone_map(other)

    def test_the_curve_joins_the_fit_and_stays_under_the_peak(self):
        thr, peak = 0.65, 3.4975
        fit = lambda x: x * (2.51 * x + 0.03) / (x * (2.43 * x + 0.59) + 0.14)
        lo, hi = 0.0, 8.0   # x0 by bisection, independent of the closed form the shader uses
        for _ in range(60):
            mid = (lo + hi) / 2
            if fit(mid) < thr: lo = mid
            else: hi = mid
        x0, h = lo, 1e-4
        self.assertEqual(OCARINA.curve(0.2), fit(0.2))                                      # below the threshold: the game's fit
        self.assertAlmostEqual(OCARINA.curve(x0 + 1e-9), thr, places=6)                      # no step at the threshold
        below = (fit(x0) - fit(x0 - h)) / h; above = (OCARINA.curve(x0 + h) - OCARINA.curve(x0 + 1e-9)) / h
        self.assertAlmostEqual(below, above, places=3)                                       # no kink
        values = [OCARINA.curve(x0 + 0.05 * i) for i in range(2000)]
        self.assertTrue(all(a < b for a, b in zip(values, values[1:])))                      # more scene light is always more output
        self.assertLess(values[-1], peak); self.assertGreater(OCARINA.curve(1000.0), peak - 1e-6)
        self.assertGreater(OCARINA.curve(7.24), 2.5)                                         # the fit's own white clip (x = 7.24) is well inside the HDR range

    def test_the_shadow_step_darkens_shadows_and_leaves_the_range_above_white(self):
        srgb_code = lambda c: c * 12.92 if c <= 0.0031308 else 1.055 * c ** (1 / 2.4) - 0.055
        for c in (0.001, 0.0031308, 0.01, 0.2, 0.9):
            self.assertAlmostEqual(OCARINA.shadows(c), srgb_code(c) ** 2.2, places=12)   # the light a 2.2 screen gives for the sRGB code
        self.assertLess(OCARINA.shadows(0.01), 0.01 * 0.7)                                 # the code 0.1: a third darker
        self.assertAlmostEqual(OCARINA.shadows(0.2), 0.2, delta=0.006)                     # mid-tones hardly move
        self.assertAlmostEqual(OCARINA.shadows(1.0 - 1e-9), 1.0, places=6)                 # no step at the paper white
        self.assertEqual(OCARINA.shadows(2.5), 2.5)                                        # highlights are the tone map's
        values = [OCARINA.shadows(i / 1000) for i in range(1001)]
        self.assertTrue(all(a < b for a, b in zip(values, values[1:])))
        self.assertEqual(OCARINA.shadows(0.0), 0.0)
        for text in ('0.0031308', '12.92', '1.055', '0.055', 'float3(2.2)'): self.assertIn(text, OCARINA.BLOCK)

    def test_the_gamut_step_is_the_p3_to_709_matrix(self):
        rows = re.findall(r'dot\(dm_out, float3\(([-0-9.]+), ([-0-9.]+), ([-0-9.]+)\)\)', OCARINA.BLOCK)
        m = [[float(v) for v in row] for row in rows]
        self.assertEqual(len(m), 3)
        for row in m: self.assertAlmostEqual(sum(row), 1.0, places=3)        # white and every grey stay where they are
        self.assertGreater(m[0][0], 1.2); self.assertLess(m[0][1], -0.2)     # P3 red lies outside BT.709: more red, less green
        self.assertIn('dm_out = float3(dot(', OCARINA.hdr_tone_map(SHADER))

    def test_the_block_and_the_python_curve_have_the_same_constants(self):
        numbers = lambda text: sorted(set(re.findall(r'\b\d+\.\d+\b', text)))
        src = (GAMES / '0400486024DEC000/shader_msl.py').read_text()
        python_curve = src[src.index('def curve('):src.index('REWRITES = ')]
        fit_constants = {'2.51', '2.43', '0.03', '0.59', '0.14', '5.02', '4.86'}
        self.assertLessEqual(fit_constants, set(numbers(OCARINA.BLOCK)))
        self.assertLessEqual(fit_constants, set(numbers(python_curve)))


if __name__ == '__main__':
    unittest.main()
