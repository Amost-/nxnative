"""Ocarina of Time's own MSL rewrites (dm/gfx/tools/dmsh_build.py profile_msl): a real HDR tone map.

With HDR output on, the game's tone-mapping pixel shader (774f2663242dbfcf, AglShader.sharcb) adds the bloom to the
linear scene, applies the SDR ACES fit x(2.51x + 0.03) / (x(2.43x + 0.59) + 0.14), clamps the result to 0..1 and then
stretches the luminance of that clipped picture above a threshold up to the peak (inverse tone mapping). Whatever the
scene held above SDR white is gone at the clamp, so highlights come out brighter but flat. The rewrite keeps the
game's result wherever its HDR parameters are unusable and otherwise gives each channel the same fit up to the
game's threshold and, above it, a shoulder computed from the scene value itself, which keeps that detail. Below
the paper white it also gives the shadows the depth a gamma 2.2 screen gives the SDR picture (SHADOWS), and it
shows the colours as the Mac's SDR window does on a Display P3 screen (WIDE).

With HDR off the game binds another shader (99d1ecbf2947464b, the fit and the clamp alone), so SDR is untouched.
Measured values and the comparison with the game's curve are in this profile's README.md ("A real HDR tone map").
"""
import re

HDR_TONE_MAP = '774f2663242dbfcf'

# The lines that replace the shader's three colour outputs. They read locals of the translated shader:
#   _155 / _151 / _167   the exposed linear scene with bloom, red / green / blue: the ACES fit's input
#   _223                 the game's threshold (uniform row 4 .y, denormals flushed): where its stretch starts, 0.65
#   PEAK                 the game's peak (uniform row 4 .x) in units of the paper white, min(peak, 3.5 x paper white)
#                        over the paper white: 3.4975 at 203 nits. The expression is taken from the game's final clamp
#   _319 / _321 / _323   the game's own result, kept when the parameters do not describe an HDR range
# Above the threshold each channel follows thr + span * (1 - exp(-(x - x0) * m / span)), span = peak - thr: it leaves
# the fit at x0 (where the fit reaches the threshold) with the fit's slope m, so there is no kink, and approaches the
# peak without reaching it, so nothing clips. Per channel, as the game's fit is, so the colours below the threshold
# are the game's and a saturated highlight moves towards white as it does under the fit.
# SHADOWS: the game's HDR window carries linear light, exactly the SDR picture's sRGB codes decoded with the sRGB
# curve (measured: the two pictures' luminance percentiles agree within a few percent down to the 1st). A television
# shows the SDR picture's codes with a gamma of 2.2, which is darker in the shadows (the code 0.1 is 2.0 nits through
# sRGB and 1.3 through 2.2 at a 203-nit white), and that is the picture the game was graded on; in HDR its shadows
# look washed out, as they do on a console. So below the paper white each channel becomes the light a 2.2 screen
# gives for its sRGB code, pow(sRGB code, 2.2). At 1.0 that is 1.0, so the range above is untouched.
# WIDE: the SDR picture this game was judged against on the Mac is the host's untagged window, which macOS shows
# without colour matching: its codes drive the screen's own primaries, Display P3 on every current Mac and iPhone
# panel, so its colours are more saturated than BT.709's, while the HDR window is colour-exact and looks flatter
# beside it. The last step reads the tone-mapped values as Display P3 and writes them in BT.709 coordinates (the
# P3-to-709 matrix; components may leave 0..1), so the game's PQ pass, which converts BT.709 to BT.2020, puts the
# P3 colour on the screen. Together with SHADOWS this is the SDR picture's contrast and colour as that window shows
# them, with the highlights of the tone map above it.
BLOCK = '''    // The profile's real HDR tone map (dm/games/0400486024DEC000/shader_msl.py): the ACES fit up to the game's
    // threshold, then a shoulder of the scene value towards the peak, instead of the game's stretch of a clipped picture.
    float dm_thr = _223;
    float dm_peak = PEAK;
    float3 dm_out = float3(_319, _321, _323);
    if (dm_peak > 1.001 && dm_thr > 0.001 && dm_thr < 0.999)
    {
        float3 dm_x = precise::max(float3(_155, _151, _167), float3(0.0));
        // x0: the root of the fit's quadratic at the threshold; dm_a > 0 because the threshold is below 1.
        float dm_a = 2.51 - 2.43 * dm_thr, dm_b = 0.03 - 0.59 * dm_thr, dm_c = -0.14 * dm_thr;
        float dm_x0 = (-dm_b + sqrt(dm_b * dm_b - 4.0 * dm_a * dm_c)) / (2.0 * dm_a);
        // The fit's slope at x0 (quotient rule), which the shoulder starts with.
        float dm_n0 = dm_x0 * (2.51 * dm_x0 + 0.03), dm_d0 = dm_x0 * (2.43 * dm_x0 + 0.59) + 0.14;
        float dm_m = ((5.02 * dm_x0 + 0.03) * dm_d0 - dm_n0 * (4.86 * dm_x0 + 0.59)) / (dm_d0 * dm_d0);
        float dm_span = dm_peak - dm_thr;
        float3 dm_fit = (dm_x * (2.51 * dm_x + 0.03)) / (dm_x * (2.43 * dm_x + 0.59) + 0.14);
        float3 dm_sh = dm_thr + dm_span * (1.0 - exp(-(dm_x - dm_x0) * dm_m / dm_span));
        dm_out = precise::clamp(select(dm_sh, dm_fit, dm_x <= float3(dm_x0)), float3(0.0), float3(dm_peak));
        // Below the paper white, the light a gamma 2.2 screen gives for the sRGB code of the value (see SHADOWS).
        float3 dm_code = select(1.055 * pow(dm_out, float3(1.0 / 2.4)) - 0.055, dm_out * 12.92, dm_out <= float3(0.0031308));
        dm_out = select(dm_out, pow(precise::max(dm_code, float3(0.0)), float3(2.2)), dm_out < float3(1.0));
        // The colours a Display P3 screen gives those values (see WIDE). No clamp: the PQ pass converts to BT.2020, which holds them.
        dm_out = float3(dot(dm_out, float3(1.2249, -0.2247, 0.0)), dot(dm_out, float3(-0.0420, 1.0419, 0.0)), dot(dm_out, float3(-0.0197, -0.0786, 1.0979)));
    }
    out.m_41.x = dm_out.x;
    out.m_41.y = dm_out.y;
    out.m_41.z = dm_out.z;
'''
# The names above are the ones the first chain gave (b-d7576061facd). SPIRV-Cross numbers a shader's locals in order, so
# a chain that adds or removes instructions before them shifts every name by the same amount and renames the output
# member (b-7b11287a1dc7: 7 lower, m_34). The rewrite therefore finds the three output lines by their shape and takes
# the other locals at their fixed distances below the red result.
OUTPUTS = re.compile(r'    out\.(m_\d+)\.x = _(\d+);\n    out\.\1\.y = _(\d+);\n    out\.\1\.z = _(\d+);\n')
REF_RED = 319                                                               # the red result's number in BLOCK
REF_NAMES = (155, 151, 167, 223, 313)                                       # the locals taken by distance: scene red / green / blue, threshold, the clamp's input


def hdr_tone_map(msl):
    """The HDR tone-mapping shader's MSL with its colour outputs replaced by BLOCK.

    The anchors are the three output lines, the game's final clamp of the red channel (whose second argument is the
    peak), the threshold local and the three scene locals. The outputs must be consecutive results (red, green, blue
    two apart, as the translation emits them) and every other local must exist at its distance from the red result.
    A source without exactly these is not the shader this was written for (another game version, or a chain that
    orders the locals differently): ValueError, which fails the shader in the build instead of compiling a guess.
    """
    outs = OUTPUTS.findall(msl)
    refused = ValueError('HDR tone map: the shader is not the one the rewrite was written for (the three colour outputs, the red clamp with the peak, and the scene and threshold locals at their distances from it)')
    if len(outs) != 1: raise refused
    member, red, green, blue = outs[0][0], int(outs[0][1]), int(outs[0][2]), int(outs[0][3])
    shift = red - REF_RED
    if (green, blue) != (red + 2, red + 4) or min(REF_NAMES) + shift <= 0: raise refused
    peak = re.search(rf'float _{red} = precise::min\(_{313 + shift}, (.+)\);\n', msl)
    if not peak or not all(f'float _{n + shift} = ' in msl for n in REF_NAMES[:4] + (321, 323)): raise refused
    # BLOCK under this source's names: every _NNN it reads moved by the shift, and the output member as found.
    block = re.sub(r'\b_(\d{3})\b', lambda m: f'_{int(m.group(1)) + shift}', BLOCK).replace('out.m_41.', f'out.{member}.')
    return OUTPUTS.sub(lambda _: block.replace('PEAK', peak.group(1)), msl)


def curve(x, thr=0.65, peak=3.4975):
    """BLOCK's curve for one channel in Python, for the tests and for reading values off it: the scene value x (the
    ACES fit's input) to the output in units of the paper white. Defaults: the game's values at 203 nits."""
    import math
    a, b, c = 2.51 - 2.43 * thr, 0.03 - 0.59 * thr, -0.14 * thr
    x0 = (-b + math.sqrt(b * b - 4 * a * c)) / (2 * a)
    if x <= x0: return x * (2.51 * x + 0.03) / (x * (2.43 * x + 0.59) + 0.14)
    n0, d0 = x0 * (2.51 * x0 + 0.03), x0 * (2.43 * x0 + 0.59) + 0.14
    m = ((5.02 * x0 + 0.03) * d0 - n0 * (4.86 * x0 + 0.59)) / (d0 * d0)
    return thr + (peak - thr) * (1 - math.exp(-(x - x0) * m / (peak - thr)))


def shadows(c):
    """BLOCK's shadow step for one channel in Python (see SHADOWS): a value in units of the paper white to the light
    a gamma 2.2 screen gives for its sRGB code; values from 1.0 up are returned as they are."""
    if c >= 1.0: return c
    code = c * 12.92 if c <= 0.0031308 else 1.055 * c ** (1 / 2.4) - 0.055
    return max(code, 0.0) ** 2.2


REWRITES = {HDR_TONE_MAP: hdr_tone_map}
