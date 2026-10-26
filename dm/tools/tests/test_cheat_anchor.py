"""scripts/cheat_anchor.py: Atmosphère cheats anchored on one build and compiled for another, on synthetic NSO files built
from real AArch64 encodings (no game files). Relocated code and data, a changed callee, a resized function, pointer
slots (RELA and RELR) and code caves are carried over; changed or relocated words, ambiguous or disagreeing evidence and
outputs this tool did not write are refused, and the emitted words are checked against the VM's encodings.
"""
import importlib.util
from pathlib import Path
import struct
import sys
import tempfile
import tomllib
import unittest
import warnings

REPO = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO / 'dm/tools'))
from nso_asm import ADRP, ADDI, B, NOP

spec = importlib.util.spec_from_file_location('cheat_anchor', REPO / 'scripts/cheat_anchor.py')
assert spec and spec.loader   # a path that exists: narrows the Optional for the type checker
ca = importlib.util.module_from_spec(spec); spec.loader.exec_module(ca)

RET = 0xd65f03c0
TEXT_END, RO, DATA, SIZE, BSS = 0x1c00, 0x2000, 0x4000, 0x6000, 0x1000   # the layout every synthetic build uses


def LDRH(rt, rn, off):
    """ldrh wt, [xn, #off]: a u16 field load, the kind of instruction the stat cheats read."""
    return 0x79400000 | (off // 2) << 10 | rn << 5 | rt


def LDRW(rt, rn, off):
    """ldr wt, [xn, #off]: a u32 load, here used as an adrp's user."""
    return 0xb9400000 | (off // 4) << 10 | rn << 5 | rt


def LDRX(rt, rn, off):
    """ldr xt, [xn, #off]: a pointer load from a .data slot."""
    return 0xf9400000 | (off // 8) << 10 | rn << 5 | rt


def MOVZ(rd, imm):
    """mov wd, #imm: distinct filler instructions around a code site."""
    return 0x52800000 | imm << 5 | rd


def BL(frm, to):
    """bl from frm to to (nso_asm.B with the link bit)."""
    return B(frm, to) | 0x80000000


def reader(start, data, field=0x1e, extra=()):
    """A function that loads a u16 field of the object at data: adrp x8; add x8, x8, lo; [extra]; ldrh w0, [x8, #field]; ret."""
    return [ADRP(8, start, data), ADDI(8, 8, data & 0xfff), *extra, LDRH(0, 8, field), RET]


def slot_reader(start, slot):
    """A function that loads the pointer in a .data slot, then a field of what it points to."""
    return [ADRP(9, start, slot), LDRX(9, 9, slot & 0xfff), LDRH(0, 9, 0x38), RET]


def image(functions, relocs=(), relr=()):
    """The memory image: functions {start: words} with an .eh_frame_hdr describing them, MOD0, and a dynamic section
    with the relative relocations, as DT_RELA entries [(slot, pointer)] and as DT_RELR slots [(slot, pointer)] (the
    pointer then lies in the slot itself, RELR's implicit addend)."""
    img = bytearray(SIZE)
    struct.pack_into('<I', img, 4, 0x20)
    img[0x20:0x24] = b'MOD0'
    struct.pack_into('<i', img, 0x24, 0x2100 - 0x20)                               # dynamic section
    struct.pack_into('<ii', img, 0x30, 0x3000 - 0x20, 0x300c + len(functions) * 8 - 0x20)
    tags = [(7, 0x2200), (8, 24 * len(relocs)), (9, 24)] + ([(36, 0x2400), (35, 8 * len(relr))] if relr else []) + [(0, 0)]
    for i, (tag, value) in enumerate(tags): struct.pack_into('<qQ', img, 0x2100 + i * 16, tag, value)
    for i, (slot, ptr) in enumerate(relocs): struct.pack_into('<QQq', img, 0x2200 + i * 24, slot, ca.R_AARCH64_RELATIVE, ptr)
    for i, (slot, ptr) in enumerate(relr):
        struct.pack_into('<Q', img, 0x2400 + i * 8, slot); struct.pack_into('<Q', img, slot, ptr)
    img[0x3000:0x3004] = bytes((1, 0x1b, 3, 0x3b))                                 # eh_frame_hdr (test_nso_match's)
    struct.pack_into('<iI', img, 0x3004, 0x3200 - 0x3004, len(functions))
    struct.pack_into('<II', img, 0x3200, 16, 0)
    img[0x3208:0x3211] = b'\x01zR\0\x04\x78\x1e\x01\x1b'
    for i, (start, words) in enumerate(sorted(functions.items())):
        struct.pack_into('<' + 'I' * len(words), img, start, *words)
        fde = 0x3240 + i * 24
        struct.pack_into('<ii', img, 0x300c + i * 8, start - 0x3000, fde - 0x3000)
        struct.pack_into('<IIiI', img, fde, 16, fde + 4 - 0x3200, start - (fde + 8), len(words) * 4)
    return img


def nso(path, functions, relocs=(), relr=(), build=b'\x11' * 8, text_end=TEXT_END):
    """Write an uncompressed NSO of image() with the usual three segments plus bss, and load it as a Build."""
    img = image(functions, relocs, relr)
    hdr = bytearray(0x100); hdr[:4] = b'NSO0'
    segs = ((0, text_end), (RO, DATA - RO), (DATA, SIZE - DATA))
    fo = 0x100
    for i, (mo, sz) in enumerate(segs):
        struct.pack_into('<III', hdr, 0x10 + i * 0x10, fo, mo, sz); fo += sz
    struct.pack_into('<I', hdr, 0x3c, BSS)
    hdr[0x40:0x48] = build
    struct.pack_into('<III', hdr, 0x60, *(sz for _, sz in segs))
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_bytes(bytes(hdr) + b''.join(bytes(img[mo:mo + sz]) for mo, sz in segs))
    return ca.Build(path)


A, B2 = b'\x11' * 8, b'\x22' * 8   # the two build IDs most tests use: 1111111111111111 and 2222222222222222


class Anchors(unittest.TestCase):
    """Import on one synthetic build, compile on another, and check the words the VM will run."""
    def setUp(self):
        """A temporary folder per test; nso_syms.load reads the NSO through an unclosed open(), its warning is noise."""
        warnings.simplefilter('ignore', ResourceWarning)
        self.tmp = tempfile.TemporaryDirectory(); self.dir = Path(self.tmp.name)

    def tearDown(self):
        """Remove the temporary folder."""
        self.tmp.cleanup()

    def build(self, name, functions, **kw):
        """A synthetic build in the temporary folder."""
        return nso(self.dir / name, functions, **kw)

    def txt(self, text, name='cheats.txt'):
        """An Atmosphère file in the temporary folder."""
        p = self.dir / name; p.write_text(text); return p

    def roundtrip(self, old, new, text, name='cheats.txt', **kw):
        """Import text on old, compile on new: (entries by name, report lines, skipped count)."""
        src, _, _ = ca.import_file(self.txt(text, name), old, **kw)
        ca.write_toml(src, self.dir / 'g.cheats.toml', name)
        _, entries, report, skipped = ca.compile_source(self.dir / 'g.cheats.toml', new)
        return {e[0]: e for e in entries}, report, skipped

    def source(self, text, name='s.cheats.toml'):
        """A hand-written source in the temporary folder."""
        p = self.dir / name; p.write_text(text); return p

    # ---- data anchors ----

    def test_data_field_follows_the_object_the_code_references(self):
        """A stat field keeps its offset from the object the code references, wherever the object moves."""
        old = self.build('a', {0x100: reader(0x100, 0x4100), 0x200: reader(0x200, 0x4100, 0x20)})
        new = self.build('b', {0x300: reader(0x300, 0x4180), 0x500: reader(0x500, 0x4180, 0x20)}, build=B2)
        got, report, skipped = self.roundtrip(old, new, '[999 strength]\n02000000 0000411E 000003E7\n')
        self.assertEqual(skipped, 0, report)
        self.assertEqual(got['999 strength'][2], [0x02000000, 0x419e, 0x3e7])   # 0x4180 + the same field offset 0x1e
        self.assertIn('2/2 refs (2 exact)', got['999 strength'][3]['how'])

    def test_the_nearest_referenced_address_wins_over_a_busier_one(self):
        """The review's silent-misplacement case: a busier neighbour must not become the base of an unrelated field."""
        # A at 0x4100 is read by two functions, the target B at 0x4200 by one; only B moves in the new build
        old = self.build('a', {0x100: reader(0x100, 0x4100), 0x200: reader(0x200, 0x4100, 0x20), 0x300: reader(0x300, 0x4200)})
        new = self.build('b', {0x100: reader(0x100, 0x4100), 0x200: reader(0x200, 0x4100, 0x20), 0x300: reader(0x300, 0x4300)}, build=B2)
        got, report, skipped = self.roundtrip(old, new, '[B]\n02000000 00004200 00000001\n')
        self.assertEqual(skipped, 0, report)
        self.assertEqual(got['B'][2][1], 0x4300); self.assertIn('weak: one reference', got['B'][3]['how'])
        self.assertTrue(any('weakly' in r for r in report))

    def test_disagreeing_or_missing_references_are_refused(self):
        """References that disagree, or too few of them, refuse the cheat instead of guessing."""
        old = self.build('a', {0x100: reader(0x100, 0x4100), 0x200: reader(0x200, 0x4100, 0x20)})
        split = self.build('b', {0x300: reader(0x300, 0x4180), 0x500: reader(0x500, 0x4240, 0x20)}, build=B2)
        got, report, skipped = self.roundtrip(old, split, '[x]\n02000000 0000411E 000003E7\n')
        self.assertEqual(skipped, 1); self.assertIn('disagree', report[0])
        one = self.build('c', {0x300: reader(0x300, 0x4180)}, build=b'\x33' * 8)
        _, report, skipped = self.roundtrip(old, one, '[x]\n02000000 0000411E 000003E7\n')
        self.assertEqual(skipped, 1); self.assertIn('only 1 of its 2', report[0])

    def test_pointer_slot_is_followed_through_its_relocation(self):
        """An object reached only through a relocated .data slot (FFCC's Mog) is found through the slot's relocation."""
        # the only code reference is to a .data slot that holds a relocated pointer to the object
        old = self.build('a', {0x100: slot_reader(0x100, 0x4008), 0x200: slot_reader(0x200, 0x4008)}, relocs=[(0x4008, 0x5000)])
        new = self.build('b', {0x400: slot_reader(0x400, 0x4010), 0x600: slot_reader(0x600, 0x4010)}, relocs=[(0x4010, 0x5400)], build=B2)
        got, report, skipped = self.roundtrip(old, new, '[Mog never tired]\n04000000 00005038 00000000\n')
        self.assertEqual(skipped, 0, report)
        self.assertEqual(got['Mog never tired'][2][:2], [0x04000000, 0x5438])
        self.assertIn('through the slot 0x4010', got['Mog never tired'][3]['how'])

    def test_two_slots_of_one_object_agree_on_the_pointer_and_relr_is_read(self):
        """Two slots of one object agree on its pointer, not on the slots, and DT_RELR relocations are read too."""
        old = self.build('a', {0x100: slot_reader(0x100, 0x4008), 0x200: slot_reader(0x200, 0x4010)}, relocs=[(0x4008, 0x5000), (0x4010, 0x5000)])
        got, report, skipped = self.roundtrip(old, old, '[Mog]\n04000000 00005038 00000000\n')
        self.assertEqual(skipped, 0, report); self.assertEqual(got['Mog'][2][1], 0x5038)
        self.assertIn('through the slots 0x4008, 0x4010', got['Mog'][3]['how'])
        new = self.build('b', {0x400: slot_reader(0x400, 0x4020), 0x600: slot_reader(0x600, 0x4028)}, relr=[(0x4020, 0x5200), (0x4028, 0x5200)], build=B2)
        _, entries, report, skipped = ca.compile_source(self.dir / 'g.cheats.toml', new)
        self.assertEqual(skipped, 0, report); self.assertEqual(entries[0][2][1], 0x5238)

    # ---- code anchors ----

    def test_code_patch_relocates_its_branch_to_the_cave_and_keeps_both_names(self):
        """An ASM cheat: guarded words, the BL to its cave re-encoded at the moved site, both on / off names kept."""
        site_words = lambda s: [0xaa1703e0, NOP, LDRH(0, 0, 0x34), RET]
        old = self.build('a', {0x100: site_words(0x100)})
        new = self.build('b', {0x900: site_words(0x900)}, build=B2, text_end=0x1800)
        cave = RO - 0x100   # the cheat's code in the padding, 0x100 before the read-only data in both builds
        on = f'[Hack - on]\n04000000 {cave:08X} D2800201\n04000000 {cave + 4:08X} D65F03C0\n04000000 00000108 {BL(0x108, cave):08X}\n'
        off = f'[Hack - off]\n04000000 00000108 {LDRH(0, 0, 0x34):08X}\n'
        got, report, skipped = self.roundtrip(old, new, on + off)
        self.assertEqual(skipped, 0, report)
        prog = got['Hack - on'][2]
        guard = [0x14050000, 0x908, LDRH(0, 0, 0x34)]   # "if it still holds the original", at the new site
        self.assertEqual(prog[-7:], guard + [0x04000000, 0x908, BL(0x908, cave), 0x20000000])
        self.assertEqual(prog[:7], [0x14050000, cave, 0, 0x04000000, cave, 0xd2800201, 0x20000000])   # cave words: "if still 0"
        self.assertEqual(got['Hack - off'][2], [0x14050000, 0x908, BL(0x908, cave), 0x04000000, 0x908, LDRH(0, 0, 0x34), 0x20000000])
        self.assertEqual(got['Hack - on'][3]['pair'], 'Hack - off')
        _, entries, _, _ = ca.compile_source(self.dir / 'g.cheats.toml', new, plain=True)
        self.assertEqual(entries[0][2][-3:], [0x04000000, 0x908, BL(0x908, cave)])   # --plain: no guards

    def test_pairs_keep_their_order_and_a_pair_that_restores_elsewhere_is_not_merged(self):
        """Merged pairs keep the file's entry order (it decides which runs last); an off entry that restores another word stays separate."""
        f = [0xaa1703e0, NOP, LDRH(0, 0, 0x34), 0x1e2e1000, RET]
        old = self.build('a', {0x100: f})
        text = '[Y - off]\n04000000 0000010C 1E2E1000\n[Y - on]\n04000000 0000010C 1E2F1000\n'
        text += '[X - on]\n04000000 0000010C 1E2F1000\n[X - off]\n04000000 00000104 D503201F\n'   # restores another word
        src, _, _ = ca.import_file(self.txt(text), old)
        self.assertEqual([c['name'] for c in src['cheats']], ['Y', 'X - on', 'X - off'])
        ca.write_toml(src, self.dir / 'g.cheats.toml', 'cheats.txt')
        _, entries, _, _ = ca.compile_source(self.dir / 'g.cheats.toml', old)
        self.assertEqual([e[0] for e in entries[:2]], ['Y - off', 'Y - on'])   # off came first in the file: it still does

    def test_changed_callee_falls_back_to_the_body_and_resized_function_to_the_window(self):
        """The two fallbacks: a changed callee is found by the body digest, a resized function by the window."""
        # the site (0x1e2e1000, an fmul) sits in the middle of the function, four distinct instructions on each side
        around = [MOVZ(k, k) for k in range(1, 5)], [MOVZ(k, k) for k in range(5, 9)]
        def f(start, callee, head=()):
            """A function with an optional head, a call to callee and the site between the two runs of distinct words."""
            return [*head, 0xaa1703e0, BL(start + 4 * (1 + len(head)), callee), LDRH(0, 0, 0x34), *around[0], 0x1e2e1000, *around[1], RET]
        site = 4 * 7   # the site's offset in f without a head
        old = self.build('a', {0x100: f(0x100, 0x400), 0x400: [MOVZ(0, 1), RET]})
        changed = self.build('b', {0x200: f(0x200, 0x600), 0x600: [MOVZ(0, 2), RET]}, build=B2)
        text = f'[Speed]\n04000000 {0x100 + site:08X} 1E2F1000\n'
        got, report, skipped = self.roundtrip(old, changed, text)
        self.assertEqual(skipped, 0, report); self.assertEqual(got['Speed'][3]['how'], 'body')
        self.assertEqual(got['Speed'][2], [0x14050000, 0x200 + site, 0x1e2e1000, 0x04000000, 0x200 + site, 0x1e2f1000, 0x20000000])
        longer = self.build('c', {0x300: f(0x300, 0x700, (NOP,)), 0x700: [MOVZ(0, 1), RET]}, build=b'\x33' * 8)
        got, report, skipped = self.roundtrip(old, longer, text)
        self.assertEqual(skipped, 0, report); self.assertEqual(got['Speed'][3]['how'], 'window'); self.assertEqual(got['Speed'][2][1], 0x304 + site)

    def test_changed_original_word_and_ambiguous_window_are_refused(self):
        """A changed site word, or a window found twice, refuses the cheat."""
        f = lambda w: [0xaa1703e0, NOP, LDRH(0, 0, 0x34), w, RET]
        old = self.build('a', {0x100: f(0x1e2e1000)})
        other = self.build('b', {0x200: f(0x1e2e9000)}, build=B2)
        _, report, skipped = self.roundtrip(old, other, '[Speed]\n04000000 0000010C 1E2F1000\n')
        self.assertEqual(skipped, 1); self.assertIn('not in this build and 0 places match', report[0])
        # two identical copies where the old build had one: neither the fingerprint (2 copies, 1 expected) nor the window decides
        twice = self.build('c', {0x400: f(0x1e2e1000), 0x800: f(0x1e2e1000)}, build=b'\x33' * 8)
        _, report, skipped = self.roundtrip(old, twice, '[Speed]\n04000000 0000010C 1E2F1000\n')
        self.assertEqual(skipped, 1); self.assertIn('2 places match', report[0])

    def test_identical_copies_are_weak_by_order_and_checked_by_their_window(self):
        """Identical copies: by order is weak, a unique window confirms it, and a window that points elsewhere refuses it."""
        f = [0xaa1703e0, NOP, LDRH(0, 0, 0x34), 0x1e2e1000, RET]
        old = self.build('a', {0x100: f, 0x300: f})   # the same zero padding around both copies: the window cannot tell them apart
        new = self.build('b', {0x500: f, 0x900: f}, build=B2)
        got, report, skipped = self.roundtrip(old, new, '[Second]\n04000000 0000030C 1E2F1000\n')
        self.assertEqual(skipped, 0, report); self.assertEqual(got['Second'][2][1], 0x90c)
        self.assertIn('copy 2 of 2 by order: weak', got['Second'][3]['how'])
        # each copy followed by a function of its own: the window identifies the copy, and contradicts a changed order
        tail = lambda k: [MOVZ(k, k), MOVZ(k, k + 1), RET]
        old = self.build('c', {0x100: f, 0x114: tail(1), 0x300: f, 0x314: tail(2)})
        same_order = self.build('d', {0x500: f, 0x514: tail(1), 0x900: f, 0x914: tail(2)}, build=B2)
        got, report, skipped = self.roundtrip(old, same_order, '[Second]\n04000000 0000030C 1E2F1000\n')
        self.assertEqual(skipped, 0, report); self.assertIn('confirmed by its window', got['Second'][3]['how'])
        swapped = self.build('e', {0x500: f, 0x514: tail(2), 0x900: f, 0x914: tail(1)}, build=b'\x33' * 8)
        _, report, skipped = self.roundtrip(old, swapped, '[Second]\n04000000 0000030C 1E2F1000\n')
        self.assertEqual(skipped, 1); self.assertIn('its window says 0x50C', report[0])

    def test_a_relocated_word_is_restored_as_this_builds_own_and_never_patched_with_old_bits(self):
        """A relocated original (an adrp's user) is restored with the new build's own word and never patched with the old build's bits."""
        g = lambda s, data: [ADRP(8, s, data), LDRW(0, 8, data & 0xfff), RET]   # ldr w0, [x8, #lo]: an adrp's user
        old = self.build('a', {0x100: g(0x100, 0x4100)})
        new = self.build('b', {0x100: g(0x100, 0x4180)}, build=B2)
        _, report, skipped = self.roundtrip(old, new, f'[Next field]\n04000000 00000104 {LDRW(0, 8, 0x104):08X}\n')
        self.assertEqual(skipped, 1); self.assertIn('relocated in this build', report[0])
        got, report, skipped = self.roundtrip(old, new, f'[Restore]\n04000000 00000104 {LDRW(0, 8, 0x100):08X}\n')
        self.assertEqual(skipped, 0, report); self.assertEqual(got['Restore'][2], [0x04000000, 0x104, LDRW(0, 8, 0x180)])

    def test_a_word_the_rewriter_changed_is_reported(self):
        """A site the rewriter changed is reported, found through the NSP script's folder layout."""
        f = [0xaa1703e0, NOP, LDRH(0, 0, 0x34), 0x1e2e1000, RET]
        old = self.build('a', {0x100: f})
        new = self.build('b/extract/v1/ExeFS/main', {0x200: f}, build=B2)   # the NSP script's layout
        rewritten = bytearray(new.img); struct.pack_into('<I', rewritten, 0x20c, 0x14000000)
        (self.dir / 'b/patched_v1').mkdir(); (self.dir / 'b/patched_v1/main.patched.bin').write_bytes(rewritten)
        new = ca.Build(self.dir / 'b/extract/v1/ExeFS/main')
        _, report, skipped = self.roundtrip(old, new, '[Speed]\n04000000 0000010C 1E2F1000\n')
        self.assertEqual(skipped, 0); self.assertTrue(any('the rewriter changed the word at 0x20C' in r for r in report), report)

    def test_width_8_cave_store_and_branch_tokens(self):
        """An 8-byte store into the cave lands low word first, and a BL token is re-encoded; out-of-range branches are refused."""
        f = [0xaa1703e0, NOP, LDRH(0, 0, 0x34), RET]
        old = self.build('a', {0x100: f})
        cave = RO - 0x40
        got, report, skipped = self.roundtrip(old, old, f'[Cave]\n08000000 {cave:08X} 11112222 33334444\n04000000 00000104 {BL(0x104, cave):08X}\n')
        self.assertEqual(skipped, 0, report)
        prog = got['Cave'][2]   # memory order: the low word at the address, the high word after it
        self.assertEqual(prog[:14], [0x14050000, cave, 0, 0x04000000, cave, 0x33334444, 0x20000000,
                                     0x14050000, cave + 4, 0, 0x04000000, cave + 4, 0x11112222, 0x20000000])
        self.assertEqual(prog[-4:-1], [0x04000000, 0x104, BL(0x104, cave)])
        with self.assertRaisesRegex(ca.AnchorError, 'out of range'): ca.encode_branch(True, 0, 1 << 28)

    def test_keypress_code_keeps_its_program_with_anchored_addresses(self):
        """A keypress-gated program keeps its words with only its address re-anchored; a glued header still starts a cheat."""
        old = self.build('a', {0x100: reader(0x100, 0x4100), 0x200: reader(0x200, 0x4100, 0x20)})
        new = self.build('b', {0x300: reader(0x300, 0x4180), 0x500: reader(0x500, 0x4180, 0x20)}, build=B2)
        got, report, skipped = self.roundtrip(old, new, '[Hold A]\n80000001\n02000000 00004104 00000001\n20000000[Next]\n01000000 00004120 00000001\n')
        self.assertEqual(skipped, 0, report)
        self.assertEqual(got['Hold A'][2], [0x80000001, 0x02000000, 0x4184, 1, 0x20000000])
        self.assertIn('Next', got)   # a header glued to the previous line still starts a cheat

    def test_build_bound_cheats_and_the_file_name_check(self):
        """Unanchorable cheats stay bound to their own build, and a file named after another build needs --assume-build."""
        old = self.build('a', {0x100: reader(0x100, 0x4100), 0x200: reader(0x200, 0x4100, 0x20)})
        new = self.build('b', {0x100: reader(0x100, 0x4100), 0x200: reader(0x200, 0x4100, 0x20)}, build=B2)
        got, report, skipped = self.roundtrip(old, new, '[Heap]\n02100000 00001234 00000001\n')   # region 1: the heap
        self.assertEqual(skipped, 1); self.assertIn('written for build 1111111111111111 only', report[0])
        with self.assertRaisesRegex(ca.AnchorError, 'names build 2222222222222222'):
            ca.import_file(self.txt('[x]\n02000000 0000411E 00000001\n', '2222222222222222.txt'), old)
        src, report, bound = ca.import_file(self.txt('[x]\n02000000 0000411E 00000001\n[h]\n02100000 00001234 00000001\n', '2222222222222222.txt'), old, assume_build=True)
        self.assertTrue(report[0].startswith('[RED] ')); self.assertEqual(bound, 1)
        self.assertEqual(src['cheats'][1]['builds'], ['2222222222222222'])   # its fixed addresses are the file's build's

    # ---- the source and the outputs ----

    def test_data_actions_and_values(self):
        """The encodings of min, set with "ask", a pointer chain (register 15 zeroed after it), decimal offsets and the refusal of signed min / max."""
        old = self.build('a', {0x100: reader(0x100, 0x4100), 0x200: reader(0x200, 0x4100, 0x20)})
        refs = ', '.join(f'{{ old = "{old.word(s):08X}", size = 0x10, at = 0x0, use = 0x4, fp = "{old.digest(s, "fp")}" }}' for s in (0x100, 0x200))
        self.source(f'''format = 1
[[cheats]]
name = "HP at least 50"
target = "d_4100+0x1C"
type = "u16"
action = "min"
value = 50
[[cheats]]
name = "Gold"
section = "Items"
target = "d_4100+0x40"
type = "u32"
action = "set"
value = "ask"
min = 0
max = 9999
default = 500
[[cheats]]
name = "Mog"
target = "[d_4100+0x8]+0x38"
type = "u32"
value = 0
[[cheats]]
name = "Signed"
target = "d_4100"
type = "s16"
action = "max"
value = 10
[[cheats]]
name = "Leading zero"
target = "d_4100+010"
type = "u8"
value = 1
[[cheats]]
name = "HP never decreases"
target = "d_4100+0x1C"
type = "s16"
action = "never-decrease"
[anchors.d_4100]
data = [{refs}]
''')
        _, entries, report, skipped = ca.compile_source(self.dir / 's.cheats.toml', old)
        got = {e[0]: e for e in entries}
        self.assertEqual(got['HP at least 50'][2], [0x12030000, 0x411c, 50, 0x02000000, 0x411c, 50, 0x20000000])
        self.assertEqual(got['Gold'][2], [0x04000000, 0x4140, 500]); self.assertEqual(got['Gold'][3]['ask'], '0..9999')
        self.assertEqual(got['Gold'][3]['once'], '1'); self.assertEqual(got['Gold'][3]['value_words'], '2')
        self.assertEqual(got['Mog'][2], [0x18060000, 0x4108, 0, 0, 0x580f0000, 0x4108, 0x780f0000, 0x38,
                                         0x640f0000, 0, 0, 0x400f0000, 0, 0, 0x20000000])   # r15 is zeroed after the chain
        self.assertEqual(got['Leading zero'][2][1], 0x410a)   # decimal 010 = 10
        nd = got['HP never decreases']   # no Atmosphère program: the host runs it from the meta row
        self.assertEqual((nd[2], nd[3]['action'], nd[3]['address'], nd[3]['type']), ([], 'never-decrease', '0:0x411C', 's16'))
        self.assertIn('nxnative only', nd[3]['how'])
        self.assertEqual(skipped, 1); self.assertIn('only unsigned types', [r for r in report if 'Signed' in r][0])
        text = ca.render(entries)
        self.assertIn('[--SectionStart:Items--]\n\n[Gold]\n04000000 00004140 000001F4\n\n[--SectionEnd:Items--]', text)
        self.assertIn('[HP never decreases]\n\n', text)   # an empty entry: an inert label on other engines
        meta = ca.meta_text('s.cheats.toml', old, entries, {}, text).split('\n')
        head = meta[2].split('\t'); row = dict(zip(head, next(l for l in meta if l.startswith('HP never')).split('\t')))
        self.assertEqual((row['action'], row['address'], row['type']), ('never-decrease', '0:0x411C', 's16'))

    def test_instruction_lengths_of_every_form(self):
        """Instruction lengths of the forms the host VM does not run yet: a wrong length would misread every later word of a community file."""
        cases = [([0x94100020], 1), ([0x94100100, 0], 2), ([0x98100100, 0, 0], 3),                  # 9: register / static value
                 ([0xA4100000], 1), ([0xA4100200, 0], 2), ([0xA4100400, 0x1234], 2),                # A: none / fixed / region + address
                 # C0TcSX..: X (bits 8-11) 0 region + address, 1 region + register, 4 a static value, 5 another register
                 ([0xC0450000, 0], 2), ([0xC0450100], 1), ([0xC0450400, 0], 2), ([0xC0850400, 0, 0], 3), ([0xC0450500], 1),
                 ([0xC1000000], 1), ([0xC2000000], 1), ([0xC3000000], 1), ([0xC4000000, 0, 0], 3),
                 ([0xFF000000], 1), ([0xFFF40000, 0], 2), ([0xFFF40400], 1)]
        for words, n in cases:
            with self.subTest(word=f'{words[0]:08X}'): self.assertEqual(ca.decode(words, 0)['n'], n)
        self.assertEqual(ca.decode([0xA4100400, 0x1234], 0)['rel'], 0x1234)
        with self.assertRaisesRegex(ca.AnchorError, 'unknown opcode'): ca.decode([0xB0000000], 0)

    def test_names_with_control_characters_survive_the_source(self):
        """Names with control characters, quotes and backslashes survive the TOML source."""
        src = {'format': 1, 'authored': '1111111111111111', 'cheats': [{'name': 'a\x01b"c\\d\x7f', 'label': True}], 'anchors': {}}
        ca.write_toml(src, self.dir / 'x.cheats.toml', 'x.txt')
        self.assertEqual(tomllib.loads((self.dir / 'x.cheats.toml').read_text())['cheats'][0]['name'], 'a\x01b"c\\d\x7f')

    def test_an_output_this_tool_did_not_write_is_never_overwritten(self):
        """Hand-made, edited or another source's .txt files are kept; only this source's unchanged output is rewritten."""
        old = self.build('a', {0x100: reader(0x100, 0x4100), 0x200: reader(0x200, 0x4100, 0x20)})
        src, _, _ = ca.import_file(self.txt('[x]\n02000000 0000411E 00000001\n'), old)
        ca.write_toml(src, self.dir / 'g.cheats.toml', 'cheats.txt')
        out = self.dir / 'cheats'; out.mkdir()
        txt = out / '1111111111111111.txt'
        txt.write_text('[mine]\n')
        src, entries, _, _ = ca.compile_source(self.dir / 'g.cheats.toml', old)
        compile = lambda path, replace=False: ca.write_compiled(out, path, old, entries, src, replace)
        compile(self.dir / 'g.cheats.toml')
        self.assertEqual(txt.read_text(), '[mine]\n'); self.assertTrue((out / '1111111111111111.txt.new').read_text().startswith('[x]'))
        compile(self.dir / 'g.cheats.toml', replace=True)
        self.assertEqual((out / '1111111111111111.txt.orig').read_text(), '[mine]\n'); self.assertTrue(txt.read_text().startswith('[x]'))
        compile(self.dir / 'g.cheats.toml')   # its own unchanged output: rewritten in place
        self.assertFalse((out / '1111111111111111.txt.new').read_text() != (out / '1111111111111111.txt').read_text())
        (out / '1111111111111111.txt.new').unlink()
        compile(self.dir / 'other.cheats.toml')   # another source's output for the same build
        self.assertTrue((out / '1111111111111111.txt.new').exists()); (out / '1111111111111111.txt.new').unlink()
        txt.write_text(txt.read_text() + '[edited]\n')   # edited since it was compiled
        lines = compile(self.dir / 'g.cheats.toml')
        self.assertIn('edited since it was compiled', lines[0]); self.assertTrue(txt.read_text().endswith('[edited]\n'))


if __name__ == '__main__': unittest.main()
