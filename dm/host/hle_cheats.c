// Atmosphère-format cheat codes (the dmnt cheat VM) applied to the running game: the `.txt` files that cheat sites share as
// atmosphere/contents/<title ID>/cheats/<build ID>.txt, loaded by the first 16 hex digits (8 bytes) of the main NSO's
// build ID (dm_main_build(), from the rewriter's fixups header). The Mac front end shows them in the window's Cheats menu
// and panel (front_mac.m); toggles are remembered per build in <build>.enabled in the cheats folder and restored at the next launch.
// The host applies the enabled cheats once per presented frame (hle_nvn.c dump_frame -> dm_cheats_present) and at a fixed
// ~60 Hz from its own thread when the game is not presenting (window minimized, graphics suspended, start-up).
// The cheat VM follows the reference implementation (Atmosphère stratosphere/dmnt/source/cheat/impl/dmnt_cheat_vm.cpp and
// docs/features/cheats.md) in word order, conditions, loops (jump-back counters) and register semantics; one deliberate
// difference: each cheat runs as its own program per pass (the reference concatenates them into one), so an unclosed
// conditional in one cheat cannot swallow the next cheat's words. Implemented opcodes: 0 store static, 1 begin
// conditional, 2 end / else, 3 loop, 4 load register static, 5 load register from memory, 6 store static to a register
// address, 7 legacy arithmetic, 8 key-press conditional, A store register to memory, C0 register conditional, C3 static
// registers (read 0x00..0x7F into a register, write a register to 0x80..0xFF; kept across passes, cleared when the file is
// loaded; on a Switch an overlay tool fills the readable ones and reads the written ones, and nothing here does yet, so a
// cheat reads 0). A cheat that uses anything else (register arithmetic 9, save / restore C1 / C2, the extended key-press C4,
// pause / resume, the debug log, or an unknown form) is turned off before it ever runs, shown in the menu with
// "(unsupported opcode N)"; only the reference's memory regions 0 (main NSO) and 1 (heap) are mapped here. Every access is
// bounds-checked against the mapped main span and the opened heap: an out-of-range access turns the cheat off and logs a
// [RED] line, and the game keeps running.
// Beyond the reference, all optional (a plain community file behaves as on a Switch):
//   - an entry without code words is a label, never a cheat: a credits line, or EdiZon's [--SectionStart:Name--] /
//     [--SectionEnd:Name--] markers, which give the entries between them a section; a header glued to the previous line's
//     last code word ("00000008[Next]", a sloppy site file) still starts a new entry
//   - <build>.meta.tsv beside the file (scripts/cheat_anchor.py compiles one with it): per entry its section, note, type,
//     on / off pair, a value the panel may set ("ask", kept in <build>.values), "set" cheats that run one pass and turn
//     themselves off, and never-decrease, a host action on a typed address that keeps the highest value seen (Atmosphère's
//     VM keeps no state of a cheat between passes, so its .txt entry is empty and other engines show an inert label)
//   - "X - on" / "X - off" entries (or a meta pair) form one switch: turning it off runs the off entry (the restore) for one
//     pass; whatever <build>.enabled says is kept as it is
//   - a dry run (dm_cheat_preview) describes what a cheat would write right now and writes nothing
//   - a master switch (the folder's .cheats-off-<title> file) and a safe mode (not on iOS): a run that ended without a
//     clean exit while cheats were on leaves the folder's .cheats-running-<title> file behind, and the next launch starts
//     with every cheat off (masters too) until the player restores the saved toggles or turns a cheat on (which restores them)
//   - <build>.enabled names a duplicate name's later entries "Name #2", "Name #3", ...; a compiled file (one with a meta
//     file) of a build without <build>.enabled takes its toggles from the newest other build's compiled from the same source
//   - a load report (dm_cheats_report): counts, duplicate names, skipped lines, Atmosphère's size limits
// Switches of this file:
//   DM_CHEATS=<folder>      cheats folder (default <DM_ROOT>/cheats; the flat layout with the Atmosphère tree under it)
//   DM_CHEATS_ANY_BUILD=1   with no file of this build, load the folder's single .txt of another build, with a warning
//   DM_CHEATS_ON=<n>,…      cheats turned on by name at launch (the menu's own toggle states stay what they were)
//   DM_CHEATS_DEBUG=1       log every applied write (cheat name, where, value)
#include "dm.h"
#include "dm_input.h"   // dm_cheats_keys, the key mask the type-8 conditional reads
#include <libkern/OSCacheControl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#if !TARGET_OS_IPHONE
#include <mach/mach.h>       // the alias mapping of main's pages (mach_vm_remap), below
#include <mach/mach_vm.h>
#include <mach/vm_prot.h>
#endif
#include <errno.h>
#include <dirent.h>
#include <unistd.h>
#include <strings.h>
#include <stdarg.h>
#include <stdatomic.h>
#include <ctype.h>

// Limits of Atmosphère's own order (0x2000 dwords of program, 256 cheats per file): no shared cheat-site file and no
// hand-made one can exhaust the arrays
#define CHEAT_MAX 256          // cheats in one file
#define INS_MAX  0x2000        // dwords of one cheat's program
#define NAME_MAX 128           // characters of a [Name] / {Name} header
#define OTHER_MAX 24           // another build's .txt files listed in the menu
#define CAND_MAX 64            // .txt files scanned in the cheats folder and its Atmosphère tree
#define VM_STEP_CAP 4000000    // instructions of one cheat in one pass (the reference has none; a runaway loop must never stall a frame)
#define VW_MAX 8               // program words holding a settable value (a min / max writes it twice, an 8-byte value is two words)
#define SKIP_MAX 64            // cheats the compiler left out (the meta file's "unresolved" rows), listed for the panel
#define SRC_MAX 8              // anchored sources (*.cheats.toml) found in the folder
#define FILE_MAX (4u << 20)    // a cheat file larger than this is not a cheat file
#define ATM_CHEATS 0x80        // Atmosphère's dmnt: cheats per file,
#define ATM_WORDS 0x100        // ... words per cheat,
#define ATM_PROGRAM 0x400      // ... and words of all enabled cheats together (the load report warns past them)

typedef struct {
    char name[NAME_MAX];       // the [Name] / {Name} header line, trimmed
    uint32_t ins[INS_MAX];     // the cheat's code words, one program run per pass
    int nins;
    uint8_t master;            // {Name} header: always on, applied first, not toggleable from the menu
    uint8_t on;                // switched on (masters always; everyone else by the menu's saved <build>.enabled state)
    uint8_t broken;            // unsupported opcode / region / width / condition, or malformed: shown disabled, never runs
    uint8_t dead;              // an out-of-range access at run time turned it off (until the next reload of the file)
    uint8_t label;             // no code words (and no meta action): a credits line or a section marker, never a cheat
    uint8_t sec_mark;          // 1 = [--SectionStart:…--], 2 = [--SectionEnd:…--]
    uint8_t once;              // meta "set": runs one pass, then turns itself off
    uint8_t restore_once;      // the off half of a pair just switched off: runs one pass (the restore), then turns itself off
    uint8_t heap_wait;         // it waited for the game's heap once (logged once)
    int junk_line;             // the first line under it that was not code words (an entry left without code is broken, not a label)
    uint8_t nd;                // meta never-decrease: the host keeps the highest value of (nd_region, nd_off), no program
    uint8_t ask;               // meta "ask": the panel may set the value held in the program words vw[]
    uint8_t weak;              // meta: scripts/cheat_anchor.py resolved one of its anchors weakly
    uint8_t pair_off;          // the off (restore) half of an on / off pair
    int pair;                  // the other half of an on / off pair, -1 none
    int dup;                   // how many earlier entries carry the same name (its <build>.enabled key is "Name #dup+1")
    char why[80];              // the disabled state the menu shows (with the reason), filled at load or at run time
    char section[NAME_MAX];    // the section it lies in ("" outside any)
    char note[200];            // the meta file's "resolved" and "note", for the panel's tooltip
    char type[8];              // the meta type (u8 … u64, s8 … s64, f32, f64), "" unknown
    char pairname[NAME_MAX];   // the meta pair's name, linked to an index after the meta file is read
    int vw[VW_MAX], nvw;       // the program words holding the value (an 8-byte value: its high word, then its low word)
    double vmin, vmax; uint8_t has_min, has_max;   // the meta ask bounds
    uint8_t nd_region; uint64_t nd_off;            // never-decrease: region 0 main / 1 heap, offset in it
    uint8_t nd_have; uint64_t nd_max;              // never-decrease: the highest value seen since it was turned on
} cheat_t;

static cheat_t g_cheat[CHEAT_MAX]; static int g_ncheat;
static char g_dir[1024];       // cheats folder (DM_CHEATS or <DM_ROOT>/cheats), "" when neither is set
static char g_path[2048];      // the loaded file (logged; "Reload cheats" re-reads exactly this path)
static char g_build[17];       // the loaded file's build ID: main's build ID cut to 16 hex digits, upper case as the
                               // cheat files name it (dmnt matches the file name case-insensitively on disk)
static char g_tid[17];         // this game's title ID (the profile's DM_GAME_PROGRAM_ID), for the Atmosphère tree
static char g_others[OTHER_MAX][17]; static int g_nothers;   // builds on disk that are not this game's build
static char g_other_ver[OTHER_MAX][24];                      // their display versions, from their meta files ("" unknown)
static char g_version[24];     // this build's display version (the profile's build rows, else the meta file), "" unknown
static char g_on[16][NAME_MAX]; static int g_non;            // the names of DM_CHEATS_ON, turned on at load time
static char g_skip_name[SKIP_MAX][NAME_MAX], g_skip_why[SKIP_MAX][160]; static int g_nskip;   // the compiler's left-outs
static char g_src[SRC_MAX][256]; static int g_nsrc;          // *.cheats.toml sources in the folder
static char g_report[4096];    // the load report (dm_cheats_report)
static int g_have_meta;        // the loaded file came with a meta file
static int g_junk, g_junk_line, g_glued;   // prose lines ignored and the first one; headers split off a code line
static char g_carried[64];     // the other build whose <build>.enabled gave the toggles ("" none)
static char g_meta_src[256];   // the source the meta file names ("compiled from <source>"), "" without a meta file
static _Atomic int g_exiting;  // dm_cheats_exit ran: no pass may write the safe-mode flag again
static _Atomic int g_active;   // a file is loaded (the per-present hook exits before taking any lock)
static _Atomic int g_master = 1;   // the master switch: 0 = no cheat runs (the folder's .cheats-off-<title> file)
static int g_safe;             // safe mode: the last run ended without a clean exit while cheats were on
static _Atomic uint64_t g_present_ns;   // the last present: the ~60 Hz thread stands down while it is recent
static _Atomic int g_dbg;      // DM_CHEATS_DEBUG
static int g_any;              // DM_CHEATS_ANY_BUILD
static _Atomic int g_inited;   // dm_cheats_init done (the thread keeps running under the consoleless iOS app too)

// Region 0: the guest main NSO as the loader mapped it (dm/host/loader.c map_image: text pages and the patch area
// read+execute, data and bss read+write, the host's key page read-only at the image's end); region 1: the heap,
// whose opened extent grows and shrinks as the game's heap does (hle_svc.c)
static module_t *g_main_mod;   // the "main" module of the profile (not an NRO), found at init; its loaded fields come from loader.c

// A second mapping of main's memory (same physical pages, mach_vm_remap with copy = false), protected read+write for the
// whole process: a cheat's write to a code page goes through it while the game's own mapping stays executable. Toggling
// the original page mprotect RW -> copy -> RX on every write races with the game's running cores: between the first
// mprotect and the restore their fetches of any instruction on that page fault (a 16 KB macOS page holds ~4 KB of
// instructions, found when main+0x305DD98 faulted while the poke page 0x305F3FC was toggled, run xa). With the alias the
// protections never change, so only the honest mid-word race the reference on Switch itself has is left. NULL when the
// remap failed: writes fall back to the per-page mprotect toggle (kept below), logged [RED] once
static uint8_t *g_alias;       // the alias mapping of main's image (same layout, page rounded up); every offset a
                               // cheat reaches is bounds-checked against main's own span first, so the page-rounded
                               // size needs no variable of its own
static int g_alias_fallback;   // the fallback [RED] was already logged once

// Map main's image a second time, writable. Called once a cheat file is actually picked (at init that is before the
// guest starts, so nothing protects or tracks these pages yet); the mapping stays for the process's lifetime, the
// loader's per-page protections never change after load. iPhone only: its SDK forbids mach_vm.h, and there the
// guarded main_write_pages falls back to the per-page mprotect toggle (unsampled, plain C must stay compiling)
#if TARGET_OS_IPHONE
static void alias_setup(void) { g_alias = NULL; }
#else
static void alias_setup(void) {
    module_t *m = g_main_mod;
    long pg = sysconf(_SC_PAGESIZE); if (pg <= 0) pg = 0x4000;   // 16 KB on Apple Silicon, a safe floor elsewhere
    uint64_t size = ((uint64_t)m->size + (uint64_t)pg - 1) & ~((uint64_t)pg - 1);   // mach_vm_remap wants whole pages
    mach_vm_address_t dst = 0;
    vm_prot_t cur = 0, mx = 0;
    kern_return_t kr = mach_vm_remap(mach_task_self(), &dst, size, 0, VM_FLAGS_ANYWHERE,
                                     mach_task_self(), (mach_vm_address_t)(uintptr_t)m->base, FALSE,
                                     &cur, &mx, VM_INHERIT_SHARE);
    if (kr) { g_alias = NULL; return; }
    // The alias's protections are independent of the original mapping's: make everything writable once. The key page
    // stays refused by the write path; the alias is only ever used by a check-passing write
    kr = mach_vm_protect(mach_task_self(), dst, size, 0, VM_PROT_READ | VM_PROT_WRITE);
    if (kr) { mach_vm_deallocate(mach_task_self(), dst, size); g_alias = NULL; return; }
    g_alias = (uint8_t *)(uintptr_t)dst;
}
#endif

// The cheats list, the toggles and one VM pass at a time
static pthread_mutex_t g_lock = PTHREAD_MUTEX_INITIALIZER;

// ---------- the dry run (dm_cheat_preview): what a cheat would write, nothing written ----------

static int g_dry;              // a dry run is in progress (under g_lock): writes are described, nothing is turned off
static char *g_dry_out; static size_t g_dry_cap, g_dry_len; static int g_dry_writes;

// One line of the dry run's description (truncated silently at the caller's buffer size)
static void dry_line(const char *fmt, ...) {
    if (!g_dry_out || g_dry_len + 1 >= g_dry_cap) return;
    va_list ap; va_start(ap, fmt);
    int n = vsnprintf(g_dry_out + g_dry_len, g_dry_cap - g_dry_len, fmt, ap);
    va_end(ap);
    if (n < 0) return;
    g_dry_len += (size_t)n < g_dry_cap - g_dry_len ? (size_t)n : g_dry_cap - g_dry_len - 1;
    if (g_dry_len + 1 < g_dry_cap) { g_dry_out[g_dry_len++] = '\n'; g_dry_out[g_dry_len] = 0; }
}

// A cheat turned itself off for good (until the file is reloaded): the menu shows it disabled with the reason. In a dry
// run the reason is only described: a preview must never change the cheat
static void cheat_kill(cheat_t *c, const char *fmt, ...) {
    va_list ap; va_start(ap, fmt);
    char msg[160]; vsnprintf(msg, sizeof msg, fmt, ap);
    va_end(ap);
    if (g_dry) { dry_line("stops: %s", msg); return; }
    if (c->dead) return;
    c->dead = 1;
    snprintf(c->why, sizeof c->why, " (off: %s)", msg);
    LOG("[RED] cheat \"%s\": %s, turning it off", c->name, msg);
}

// ---------- decode: one decoder for both the load verdict and the run ----------

// The Atmosphère opcode of the instruction starting at *p: a nibble, extended by the second and third nibble for the
// 0xC / 0xF forms (register conditionals; pause / resume / debug log), the way the reference DecodeNextOpcode does it
static unsigned op_kind(uint32_t w) {
    unsigned op = w >> 28;
    if (op >= 0xC) op = (op << 4) | ((w >> 24) & 0xF);
    if (op >= 0xF0) op = (op << 4) | ((w >> 20) & 0xF);
    return op;
}

// Conditional begins (1 / 8 / C0 / C4): when a failed conditional is skipped, its whole nested block must be walked to its
// own end / else, so each of these increases the depth counter
static int op_cond_begin(unsigned op) { return op == 1 || op == 8 || op == 0xC0 || op == 0xC4; }

// Unsupported opcode, with the reference's own opcode name in the menu label ("unsupported opcode 9", "… FF0")
static int ins_unsupported(cheat_t *c, const uint32_t *p) {
    snprintf(c->why, sizeof c->why, " (unsupported opcode %X)", op_kind(p[0]));
    c->broken = 1;
    return 0;
}

// One unsupported verdict, of the reasons the reference can still decode but the host does not run
#define UNSUP(c, what) { snprintf((c)->why, sizeof (c)->why, " (%s)", what); (c)->broken = 1; return 0; }

// The instruction the way the run and the load verdict must both see it: fields from the reference's decode, one place.
// rel = the 40-bit (36-bit for A / C0) relative address, val = the static value / a loop's iterations / the key mask;
// s = the source register (A) or the compared register (C0), o = the offset type (A) or the operand type (C0)
typedef struct {
    unsigned op, len, t, m, r, x, c, flags, s, o;
    uint64_t rel, val;
} ins_t;

// The width nibble every sized form shares: 1, 2, 4 or 8 bytes
static int width_ok(unsigned t) { return t == 1 || t == 2 || t == 4 || t == 8; }

// Decode the instruction at p (n words left) or 0 when it cannot run here (c->why: why). Mirrors the reference
// DecodeNextOpcode field by field, so the run never miscounts a word; outside what the host implements
// (opcodes 0..8, A, C0, C3 with the reference's value widths and its six comparisons) the verdict is unsupported
static int ins_dec(cheat_t *c, const uint32_t *p, int n, ins_t *o) {
    unsigned t;
    if (n <= 0) UNSUP(c, "truncated");
    memset(o, 0, sizeof *o);
    uint32_t w = p[0];
    o->op = op_kind(w); o->len = 1;
    switch (o->op) {
        case 0: {   // 0TMR00AA AAAAAAAA VVVVVVVV (VVVVVVVV): store the value at memory base + rel + reg[r]
                    // (the reference adds the offset register unconditionally: all registers start at 0)
            if ((t = (w >> 24) & 0xF, !width_ok(t))) UNSUP(c, "width");
            if ((o->m = (w >> 20) & 0xF) > 1) UNSUP(c, "region");
            o->t = t; o->r = (w >> 16) & 0xF;
            if (n < 2) UNSUP(c, "truncated");
            o->rel = ((uint64_t)(w & 0xFF) << 32) | p[1];
            o->len = 3;
            if (o->t == 8) {   // a width-8 value comes in the reference's word order: first dword high, second low
                if (n < 4) UNSUP(c, "truncated");
                o->val = ((uint64_t)p[2] << 32) | p[3]; o->len = 4;
            } else o->val = p[2];
        } break;
        case 1: {   // 1TMCXrAA AAAAAAAA VVVVVVVV (VVVVVVVV): compare memory at base + rel (+ reg[x] for X=1) with the value
            if ((t = (w >> 24) & 0xF, !width_ok(t))) UNSUP(c, "width");
            if ((o->m = (w >> 20) & 0xF) > 1) UNSUP(c, "region");
            o->t = t; o->c = (w >> 16) & 0xF;
            if (o->c < 1 || o->c > 6) UNSUP(c, "condition");   // only the six comparisons run
            o->flags = ((w >> 12) & 0xF) != 0;                 // X, taken as a boolean like the reference does
            o->x = (w >> 8) & 0xF;
            if (n < 2) UNSUP(c, "truncated");
            o->rel = ((uint64_t)(w & 0xFF) << 32) | p[1];
            o->len = 3;
            if (o->t == 8) {
                if (n < 4) UNSUP(c, "truncated");
                o->val = ((uint64_t)p[2] << 32) | p[3]; o->len = 4;
            } else o->val = p[2];
        } break;
        case 2:     // 2X000000: end of a conditional, else for X = 1 (the reference reads it as an else flag)
            o->flags = ((w >> 24) & 0xF) == 1;
            break;
        case 3: {   // 300R0000 VVVVVVVV starts (the reference's Loop, reg r counted), 310R0000 ends (the same r again;
                    // any X but 0 at nibble 1 is the end form, the way DecodeNextOpcode reads start_loop == 0)
            o->flags = ((w >> 24) & 0xF) != 0;
            o->r = (w >> 16) & 0xF;
            if (!o->flags) {
                if (n < 2) UNSUP(c, "truncated");
                o->val = p[1]; o->len = 2;
            }
        } break;
        case 4: {   // 400R0000 VVVVVVVV VVVVVVVV: reg[r] = the 64-bit value
            if (n < 3) UNSUP(c, "truncated");
            o->r = (w >> 16) & 0xF;
            o->val = ((uint64_t)p[1] << 32) | p[2]; o->len = 3;
        } break;
        case 5: {   // 5TMR00AA / 5T0R10AA / 5T0R2SAA / 5TMR3SAA AAAAAAAA: reg[r] = the width bytes of one address
            if ((t = (w >> 24) & 0xF, !width_ok(t))) UNSUP(c, "width");
            o->t = t; o->m = (w >> 20) & 0xF; o->r = (w >> 16) & 0xF;
            o->flags = (w >> 12) & 0xF; o->x = (w >> 8) & 0xF;   // flags: 0 fixed, 1 reg[r] + rel, 2 reg[x] + rel, 3 region + reg[x] + rel
            if (o->flags > 3) UNSUP(c, "operand");
            if ((o->flags == 0 || o->flags == 3) && o->m > 1) UNSUP(c, "region");
            if (n < 2) UNSUP(c, "truncated");
            o->rel = ((uint64_t)(w & 0xFF) << 32) | p[1]; o->len = 2;
        } break;
        case 6: {   // 6T0RIor0 VVVVVVVV VVVVVVVV: the value at reg[r] (+ reg[x] for o=1), reg[r] + width for I=1
            if ((t = (w >> 24) & 0xF, !width_ok(t))) UNSUP(c, "width");
            if (n < 3) UNSUP(c, "truncated");
            o->t = t; o->r = (w >> 16) & 0xF;
            o->flags = (((w >> 12) & 0xF) != 0) | (((w >> 8) & 0xF) != 0) << 1;   // 1 = increment reg[r], 2 = add reg[x]
            o->x = (w >> 4) & 0xF;
            o->val = ((uint64_t)p[1] << 32) | p[2]; o->len = 3;
        } break;
        case 7: {   // 7T0RC000 VVVVVVVV: reg[r] performs the width arithmetic with the value
            if ((t = (w >> 24) & 0xF, !width_ok(t))) UNSUP(c, "width");
            if ((o->c = (w >> 12) & 0xF) > 4) UNSUP(c, "arithmetic");   // the five legacy operations
            o->t = t; o->r = (w >> 16) & 0xF;
            if (n < 2) UNSUP(c, "truncated");
            o->val = p[1]; o->len = 2;
        } break;
        case 8:     // 8kkkkkkk: every key of the mask held; the DM_BTN_* bit order, the sticks' directions on 16..23
                    // (dm_input.h); SL / SR on 24 / 25 can never be held, no input source of this host reports them
            o->val = w & 0x0FFFFFFFu;
            break;
        case 0xA: { // ATSRIOxa (aaaaaaaa): store reg[s] (width T) at an address from reg[r] and the offset type O:
                    // 0 reg[r], 1 reg[r] + reg[x], 2 reg[r] + a, 3 region x + reg[r], 4 region x + a, 5 region x + reg[r] + a;
                    // I (flags) adds the width to reg[r] afterwards
            if ((t = (w >> 24) & 0xF, !width_ok(t))) UNSUP(c, "width");
            o->t = t; o->s = (w >> 20) & 0xF; o->r = (w >> 16) & 0xF;
            o->flags = ((w >> 12) & 0xF) != 0; o->o = (w >> 8) & 0xF; o->x = (w >> 4) & 0xF;
            if (o->o > 5) UNSUP(c, "operand");
            if (o->o >= 3) { o->m = o->x; if (o->m > 1) UNSUP(c, "region"); }
            if (o->o == 2 || o->o == 4 || o->o == 5) {
                if (n < 2) UNSUP(c, "truncated");
                o->rel = ((uint64_t)(w & 0xF) << 32) | p[1]; o->len = 2;
            }
        } break;
        case 0xC0: {   // C0TcSX..: compare reg[s] (width T) with operand X under condition c, a conditional block like 1:
                       // 0 memory region M + a, 1 region M + reg[r], 2 reg[R] + a, 3 reg[R] + reg[r], 4 a static value,
                       // 5 another register
            if ((t = (w >> 20) & 0xF, !width_ok(t))) UNSUP(c, "width");
            o->t = t; o->c = (w >> 16) & 0xF;
            if (o->c < 1 || o->c > 6) UNSUP(c, "condition");
            o->s = (w >> 12) & 0xF; o->o = (w >> 8) & 0xF;
            switch (o->o) {
                case 0: case 1:
                    if ((o->m = (w >> 4) & 0xF) > 1) UNSUP(c, "region");
                    if (o->o == 1) { o->x = w & 0xF; break; }
                    if (n < 2) UNSUP(c, "truncated");
                    o->rel = ((uint64_t)(w & 0xF) << 32) | p[1]; o->len = 2;
                    break;
                case 2:
                    o->r = (w >> 4) & 0xF;
                    if (n < 2) UNSUP(c, "truncated");
                    o->rel = ((uint64_t)(w & 0xF) << 32) | p[1]; o->len = 2;
                    break;
                case 3: o->r = (w >> 4) & 0xF; o->x = w & 0xF; break;
                case 4:
                    if (n < (t == 8 ? 3 : 2)) UNSUP(c, "truncated");
                    o->val = t == 8 ? ((uint64_t)p[1] << 32) | p[2] : p[1]; o->len = t == 8 ? 3 : 2;
                    break;
                case 5: o->x = (w >> 4) & 0xF; break;
                default: UNSUP(c, "operand");
            }
        } break;
        case 0xC3:  // C3000XXx: static register XX: 0x00..0x7F read into reg[x], 0x80..0xFF written from reg[x]
            o->x = (w >> 4) & 0xFF; o->r = w & 0xF;
            break;
        default:    // 9, B, C1, C2, C4, F... and any unknown form
            return ins_unsupported(c, p);
    }
    if (o->len > (unsigned)n) UNSUP(c, "truncated");   // the cheat's words end in the middle of an instruction
    return (int)o->len;
}

// ---------- guest memory: the spans a cheat may touch, and the accesses into them ----------

// The span that contains the host pointer range [addr, addr+len). kind 0 = main's mapped image, kind 1 = the currently
// opened heap; NULL when any byte of the range is unmapped (rel_base is optional: callers that log only the raw guest
// address pass NULL)
static uint8_t *span_get(uint64_t addr, uint64_t len, int *kind, uint64_t *rel_base) {
    if (g_main_mod) {
        uint64_t b = (uint64_t)(uintptr_t)g_main_mod->base, off = addr - b;
        if (addr >= b && off < g_main_mod->size && len <= g_main_mod->size - off) {
            *kind = 0; if (rel_base) *rel_base = b; return (uint8_t *)(uintptr_t)addr;
        }
    }
    uint64_t hb; size_t hopen; dm_guest_heap_range(&hb, &hopen);
    if (hb && hopen && addr >= hb && addr - hb < hopen && len <= hopen - (addr - hb)) {
        *kind = 1; if (rel_base) *rel_base = hb; return (uint8_t *)(uintptr_t)addr;
    }
    return NULL;
}

// Cheats writing into main's pages (dmnt's WriteCheatProcessMemoryUnsafe on this host): if the writable alias of main
// was mapped at init (alias_setup), everything is copied through it — the same physical memory, the game's own mapping
// stays untouched and executable, no mprotect at write time. Without the alias (a remap failure) the code pages (text
// to its text_end, the patch area) are toggled writable, copied and put back per page, and the instruction cache is
// invalidated, so the game's fetches see exactly what the cheat says (the rewriter may have rewritten the same
// instruction; the cheat still overwrites it when enabled) — but that path races with the game's running cores (see
// alias_setup), so it logs a [RED] once and is truly a last resort. The key page (this host's TLS slot numbers, inside
// the mapped image) is refused either way: changing it would break every guest thread
static int main_write_pages(cheat_t *c, uint64_t addr, uint64_t len, const void *src) {
    static long pg; if (!pg) pg = getpagesize();
    module_t *m = g_main_mod; uint64_t mb = (uint64_t)(uintptr_t)m->base;
    uint64_t rx_end = (m->text_end + pg - 1) & ~(uint64_t)(pg - 1);                    // the text as mprotect'd at load
    // The patch area when it follows the image (patch_off >= 0), page-rounded. When it lies before the base
    // (patch_off < 0, the loader's large-image layout) m->size excludes it and no cheat write can reach it: po = size
    // leaves the second code range below empty. UINT64_MAX there would wrap mb + po to mb - 1, make every page count
    // as code in the fallback (a [mb - 1, ...) test) and seal data / bss pages R|X, which faults the game's next write
    uint64_t po = m->patch_off >= 0 ? ((uint64_t)m->patch_off & ~(uint64_t)(pg - 1)) : (uint64_t)m->size;
    uint64_t kp0 = mb + m->key_page_off, kp1 = kp0 + m->key_page_size;
    if (addr < kp1 && addr + len > kp0) {   // the write would cover the key page: refuse it like an out-of-range access
        cheat_kill(c, "write into the host key page is refused");
        return -1;
    }
    dm_guest_write_prepare((void *)(uintptr_t)addr, len);   // the write-protect dirty tracking must see this write coming
    const uint8_t *v = src;
    uint64_t start = addr;                  // kept for the icache invalidate: the fallback loop walks addr past it
    if (g_alias) {
        memcpy(g_alias + (size_t)(addr - mb), v, len);   // through the writable alias, the same image offset
    } else {
        if (!g_alias_fallback) { g_alias_fallback = 1; LOG("[RED] cheats: no writable alias of main, code pages go through an mprotect toggle that races with the game's own execution"); }
        for (uint64_t end = addr + len; addr < end;) {
            uint64_t p0 = addr & ~(uint64_t)(pg - 1), hi = p0 + pg < end ? p0 + pg : end;   // the slice of this page
            void *page = (void *)(uintptr_t)p0;
            int code = p0 < mb + rx_end || (p0 >= mb + po && p0 < mb + m->size);
            if (code) {
                if (mprotect(page, pg, PROT_READ | PROT_WRITE)) { cheat_kill(c, "mprotect of a code page failed (errno %d)", errno); return -1; }
                memcpy((void *)(uintptr_t)addr, v + (addr - start), hi - addr);
                if (mprotect(page, pg, PROT_READ | PROT_EXEC)) { cheat_kill(c, "mprotect restore failed (errno %d)", errno); return -1; }
            } else memcpy((void *)(uintptr_t)addr, v + (addr - start), hi - addr);
            addr = hi;
        }
    }
    sys_icache_invalidate((void *)(uintptr_t)start, len);   // the game's own fetches must see the new instructions
    return 0;
}

// Read len bytes at a guest address without any consequence for a cheat: 0 and the value, or -1 when unmapped (the dry run
// and the preview's current values use it)
static int peek(uint64_t addr, uint64_t len, uint64_t *out) {
    int kind = -1; uint64_t v = 0;
    if (!span_get(addr, len, &kind, NULL)) return -1;
    if (kind == 1) { if (dm_guest_heap_read(addr, &v, len)) return -1; }
    else memcpy(&v, (void *)(uintptr_t)addr, len);
    *out = v;
    return 0;
}

// A guest address the way a player reads it: main+0x…, heap+0x… or the bare address
static void addr_name(uint64_t addr, char *out, size_t n) {
    int kind = -1; uint64_t base = 0;
    if (span_get(addr, 1, &kind, &base)) snprintf(out, n, "%s+0x%llX", kind == 0 ? "main" : "heap", (unsigned long long)(addr - base));
    else snprintf(out, n, "0x%llX", (unsigned long long)addr);
}

// The width in bytes of a meta type ("u16" -> 2), 0 when unknown
static unsigned type_width(const char *t) { int b = atoi(t + (t[0] ? 1 : 0)); return b == 8 || b == 16 || b == 32 || b == 64 ? (unsigned)b / 8 : 0; }

// A value as the meta type of its cheat reads it (unsigned, signed, float), or unsigned decimal and hex when the type is
// unknown or does not match the width (a code word reads best in hex)
static void value_text(const cheat_t *c, unsigned width, uint64_t v, char *out, size_t n) {
    char k = c->type[0]; int tw = (int)type_width(c->type);
    if (k == 'f' && tw == (int)width && width == 4) { uint32_t u = (uint32_t)v; float f; memcpy(&f, &u, 4); snprintf(out, n, "%g", f); return; }
    if (k == 'f' && tw == (int)width && width == 8) { double d; memcpy(&d, &v, 8); snprintf(out, n, "%g", d); return; }
    if (k == 's' && tw == (int)width) { int sh = 64 - 8 * (int)width; snprintf(out, n, "%lld", (long long)((int64_t)(v << sh) >> sh)); return; }
    if (k == 'u' && tw == (int)width) { snprintf(out, n, "%llu", (unsigned long long)v); return; }
    snprintf(out, n, "%llu (0x%llX)", (unsigned long long)v, (unsigned long long)v);
}

// dmnt's WriteCheatProcessMemoryUnsafe for this host: val's low len bytes, little-endian (guest aarch64 = host arm64),
// into the span. A refusal turns the cheat off (cheat_kill) and logs a [RED] line; the game keeps running. The guest
// address is logged as the cheat VM computes it (region base + rel + offset register), which is what the player reads
// in the cheat file's own terms. In a dry run the write is described (where, the value there now, the new value) instead
static void cheat_write(cheat_t *c, uint64_t addr, uint64_t len, uint64_t val) {
    int kind = -1;
    if (!span_get(addr, len, &kind, NULL)) { cheat_kill(c, "out of mapped memory: write to guest address 0x%llx", (unsigned long long)addr); return; }
    if (g_dry) {
        char where[48], now[48], new_[48]; uint64_t cur = 0;
        addr_name(addr, where, sizeof where);
        if (peek(addr, len, &cur)) snprintf(now, sizeof now, "?"); else value_text(c, (unsigned)len, cur, now, sizeof now);
        value_text(c, (unsigned)len, val, new_, sizeof new_);
        dry_line("%s (%llu bytes): %s -> %s%s", where, (unsigned long long)len, now, new_, cur == val ? " (already)" : "");
        g_dry_writes++;
        return;
    }
    if (atomic_load(&g_dbg)) LOG("cheat \"%s\": write %llu bytes of 0x%llx at guest address 0x%llx (%s)", c->name, (unsigned long long)len, (unsigned long long)val, (unsigned long long)addr, kind == 0 ? "main NSO" : "heap");
    if (kind == 0) main_write_pages(c, addr, len, &val);
    // The heap write happens under the memory lock (dm_guest_heap_write), so a concurrent SetHeapSize cannot shrink it
    // out from under the copy; it only refuses if the span shrank since the span check a moment ago: out of range as ever
    else if (dm_guest_heap_write(addr, &val, len)) cheat_kill(c, "out of mapped memory: write to guest address 0x%llx", (unsigned long long)addr);
}

// dmnt's ReadCheatProcessMemoryUnsafe for this host: the mapped main span and the opened heap are both readable; the
// value is assembled zero-extended little-endian
static int cheat_read(cheat_t *c, uint64_t addr, uint64_t len, uint64_t *out) {
    int kind = -1;
    if (!span_get(addr, len, &kind, NULL)) { cheat_kill(c, "out of mapped memory: read at guest address 0x%llx", (unsigned long long)addr); return -1; }
    uint64_t v = 0;
    // The heap read is hole-free like its write counterpart: a span that shrank since the span check refuses here
    // instead of faulting on a page a concurrent SetHeapSize mprotect'd away
    if (kind == 1) { if (dm_guest_heap_read(addr, &v, len)) { cheat_kill(c, "out of mapped memory: read at guest address 0x%llx", (unsigned long long)addr); return -1; } }
    else memcpy(&v, (void *)(uintptr_t)addr, len);
    *out = v;
    return 0;
}

// ---------- the cheat VM: one pass ----------

static uint64_t g_reg[16], g_looptop[16];   // the reference's registers and loop tops (its saved values belong to C1/C2, not implemented)
static uint64_t g_static[256];              // the reference's static registers (C3): kept across passes, cleared on load

// Region base for kind m: 0 main NSO, 1 heap. The caller checks region_ready(m) first: with no span open the base is
// 0, and a cheat resolved against 0 could by luck fall inside main's mapped span, which an out-of-range-style [RED]
// line then does not explain
static uint64_t region_base(int m) {
    if (m == 0) return g_main_mod ? (uint64_t)(uintptr_t)g_main_mod->base : 0;
    uint64_t hb; size_t hopen; dm_guest_heap_range(&hb, &hopen);
    return hb && hopen ? hb : 0;
}

// The named region must have its span open right now: a cheat that names the heap (region 1) before the game's first
// SetHeapSize would compute its addresses from base 0, so its pass stops here and it waits (logged once): a cheat turned
// on from <build>.enabled at launch runs as soon as the game opens its heap instead of being turned off before that
static int region_ready(cheat_t *c, int m) {
    if (m == 0) return g_main_mod != NULL;   // main is always mapped by the time a cheat file was picked
    uint64_t hb; size_t hopen; dm_guest_heap_range(&hb, &hopen);
    if (hb && hopen) return 1;
    if (g_dry) dry_line("waits: region 1 (heap) has no span opened yet");
    else if (!c->heap_wait) { c->heap_wait = 1; LOG("cheats: \"%s\" waits for the game's heap (region 1 has no span opened yet)", c->name); }
    return 0;
}

// Skipping a failed / finished conditional the reference's way: walk nested begins and ends (each counted once at its
// decode), and a not-taken if also meets its else at the same depth as the skip's end (the else block is skipped too)
static int vm_skip(cheat_t *c, const uint32_t *ins, int nins, int *pidx, int *pdepth, int is_if) {
    int desired = *pdepth - 1;
    while (*pdepth > desired && *pidx < nins) {
        ins_t in;
        int len = ins_dec(c, ins + *pidx, nins - *pidx, &in);
        if (len <= 0) return -1;      // validated before the first pass; keep the walk safe anyway
        if (op_cond_begin(in.op)) (*pdepth)++;
        else if (in.op == 2) {
            if (!in.flags) (*pdepth)--;
            else if (is_if && *pdepth - 1 == desired) { *pidx += len; return 0; }   // an else of a not-taken if: stop there
        }
        *pidx += len;
    }
    return 0;
}

// The width's mask for conditions and arithmetic results (the reference truncates to the width)
static uint64_t width_mask(unsigned t) { return t == 8 ? UINT64_MAX : (1ull << (8 * t)) - 1; }

// The six comparisons in the reference's number order (opcodes 1 and C0, both unsigned): 1 >, 2 >=, 3 <, 4 <=, 5 ==, 6 !=
static int cond_met(unsigned cond, uint64_t got, uint64_t want) {
    return cond == 1 ? got > want : cond == 2 ? got >= want : cond == 3 ? got < want :
           cond == 4 ? got <= want : cond == 5 ? got == want : got != want;
}

// One pass of cheat c; the VM state is whatever the caller reset. Returns -1 when the cheat killed itself (its
// word-boundary verdicts already marked it broken at load; a skip over a shuffled word could still fail here)
static int vm_run(cheat_t *c) {
    const uint32_t *ins = c->ins; int nins = c->nins;
    int idx = 0, depth = 0;   // like the reference Execute: one instruction pointer, one conditional depth
    long steps = 0;
    while (idx < nins) {
        if (++steps > VM_STEP_CAP) { cheat_kill(c, "over %d instructions in one pass: runaway loop", VM_STEP_CAP); return -1; }
        ins_t in;
        int len = ins_dec(c, ins + idx, nins - idx, &in);
        if (len <= 0) { cheat_kill(c, "malformed instruction at word %d%s", idx, c->why); return -1; }
        switch (in.op) {
            case 0: {   // static store: base + rel + reg[r] (the bounds check is the span check inside cheat_write)
                if (!region_ready(c, in.m)) return -1;
                cheat_write(c, region_base(in.m) + in.rel + g_reg[in.r], in.t, in.val & width_mask(in.t));
            } break;
            case 8: case 1: {   // key-press conditional (8) / memory conditional (1): depth counted like the reference, before the verdict
                depth++;
                int met = 1, run = 1;
                if (in.op == 8) {
                    met = (dm_cheats_keys() & in.val) == in.val;   // every key of the mask held
                } else {
                    if (!region_ready(c, in.m)) return -1;   // the conditional reads the region it names
                    uint64_t src = 0;
                    if (cheat_read(c, region_base(in.m) + in.rel + (in.flags ? g_reg[in.x] : 0), in.t, &src) == 0)
                        met = cond_met(in.c, src & width_mask(in.t), in.val & width_mask(in.t));
                    else run = 0;   // the read could not be done: the cheat is off (cheat_read logged the [RED] line)
                }
                if (!run) return -1;
                if (!met) { idx += len; if (vm_skip(c, ins, nins, &idx, &depth, 1)) return -1; continue; }   // block (else too) skipped
            } break;
            case 0xC0: {   // register conditional: reg[s] against memory, a static value or another register, a block like 1's
                depth++;
                uint64_t want = 0, got = g_reg[in.s] & width_mask(in.t);
                int ok = 0;
                switch (in.o) {
                    case 0: if (!region_ready(c, in.m)) return -1; ok = cheat_read(c, region_base(in.m) + in.rel, in.t, &want); break;
                    case 1: if (!region_ready(c, in.m)) return -1; ok = cheat_read(c, region_base(in.m) + g_reg[in.x], in.t, &want); break;
                    case 2: ok = cheat_read(c, g_reg[in.r] + in.rel, in.t, &want); break;
                    case 3: ok = cheat_read(c, g_reg[in.r] + g_reg[in.x], in.t, &want); break;
                    case 4: want = in.val; break;
                    default: want = g_reg[in.x]; break;
                }
                if (ok) return -1;   // a memory operand could not be read: the cheat is off (cheat_read logged it)
                if (!cond_met(in.c, got, want & width_mask(in.t))) { idx += len; if (vm_skip(c, ins, nins, &idx, &depth, 1)) return -1; continue; }
            } break;
            case 2:   // end / else of a conditional: an else skips its block, a plain end closes the block
                if (in.flags) {   // an else: skip its block like the reference; an else at depth 0 is mismatched, and
                                  // the reference treats that as a VM error (SkipConditionalBlock aborts at depth 0)
                    if (depth == 0) { cheat_kill(c, "mismatched else at conditional depth 0"); return -1; }
                    idx += len; if (vm_skip(c, ins, nins, &idx, &depth, 0)) return -1; continue;
                }
                if (depth > 0) depth--;   // a plain end (nop at depth 0, the reference's own gracious assumption)
                break;
            case 3:   // loop: start (counter set, jump-back point kept), end (decrement, jump back until it reaches 0)
                if (!in.flags) { g_reg[in.r] = in.val; g_looptop[in.r] = idx + 2; idx += (int)in.len; continue; }
                g_reg[in.r]--;
                if (g_reg[in.r]) { idx = (int)g_looptop[in.r]; continue; }
                break;
            case 4:   // register = static 64-bit value
                g_reg[in.r] = in.val;
                break;
            case 5: {   // register = the width bytes of one address (fixed, by register, or region + register, the reference's four forms)
                uint64_t addr, v0 = 0;
                switch (in.flags) {
                    case 0: if (!region_ready(c, in.m)) return -1; addr = region_base(in.m) + in.rel; break;
                    case 1: addr = g_reg[in.r] + in.rel; break;
                    case 2: addr = g_reg[in.x] + in.rel; break;
                    default: if (!region_ready(c, in.m)) return -1; addr = region_base(in.m) + g_reg[in.x] + in.rel; break;
                }
                if (cheat_read(c, addr, in.t, &v0) == 0) g_reg[in.r] = v0 & width_mask(in.t);
                else return -1;   // the load could not be done: the cheat is off (cheat_read logged it)
            } break;
            case 6: {   // store the value at reg[r] (+ reg[x] for o=1); reg[r] gains the width for I=1, like the reference
                cheat_write(c, g_reg[in.r] + (in.flags & 2 ? g_reg[in.x] : 0), in.t, in.val & width_mask(in.t));
                if (in.flags & 1) g_reg[in.r] += in.t;
            } break;
            case 7: {   // register arithmetic the reference's order: the full dword (its u64 zero-extension) goes into
                        // the operation and only the result is truncated to the width, as its ((u8)(reg - 0x100)) does
                        // (masking the operand to the width first happens to give the same add / sub / mul, but there
                        // is no reason to rely on that). The shift counts are masked to 63 bits, aarch64's LSLV / LSRV
                uint64_t v = in.val, r = g_reg[in.r];
                switch (in.c) {
                    case 0: r += v; break;   // 0 add
                    case 1: r -= v; break;   // 1 sub
                    case 2: r *= v; break;   // 2 mul
                    case 3: r <<= (v & 63); break;   // 3 lsl
                    case 4: r >>= (v & 63); break;   // 4 lsr
                }
                g_reg[in.r] = r & width_mask(in.t);
            } break;
            case 0xA: {   // store register: reg[s] (width) at the address of the offset type, reg[r] += width for I=1
                uint64_t addr;
                switch (in.o) {
                    case 0: addr = g_reg[in.r]; break;
                    case 1: addr = g_reg[in.r] + g_reg[in.x]; break;
                    case 2: addr = g_reg[in.r] + in.rel; break;
                    case 3: if (!region_ready(c, in.m)) return -1; addr = region_base(in.m) + g_reg[in.r]; break;
                    case 4: if (!region_ready(c, in.m)) return -1; addr = region_base(in.m) + in.rel; break;
                    default: if (!region_ready(c, in.m)) return -1; addr = region_base(in.m) + g_reg[in.r] + in.rel; break;
                }
                cheat_write(c, addr, in.t, g_reg[in.s] & width_mask(in.t));
                if (in.flags) g_reg[in.r] += in.t;
            } break;
            case 0xC3:   // static registers: 0x00..0x7F are read into a register, 0x80..0xFF written from one
                if (in.x < 0x80) g_reg[in.r] = g_static[in.x]; else g_static[in.x] = g_reg[in.r];
                break;
            default:
                cheat_kill(c, "instruction the VM does not run reached it");   // cannot happen: validation turned the cheat off
                return -1;
        }
        idx += len;
    }
    return 0;
}

// ---------- host actions: never-decrease ----------

// a < b in the cheat's meta type: unsigned, signed (sign-extended from its width) or float (a NaN compares false, so it is
// never written back over)
static int value_less(const cheat_t *c, unsigned width, uint64_t a, uint64_t b) {
    if (c->type[0] == 'f' && width == 4) { uint32_t ua = (uint32_t)a, ub = (uint32_t)b; float x, y; memcpy(&x, &ua, 4); memcpy(&y, &ub, 4); return x < y; }
    if (c->type[0] == 'f' && width == 8) { double x, y; memcpy(&x, &a, 8); memcpy(&y, &b, 8); return x < y; }
    if (c->type[0] == 's') { int sh = 64 - 8 * (int)width; return (int64_t)(a << sh) >> sh < (int64_t)(b << sh) >> sh; }
    return a < b;
}

// One never-decrease pass: the first pass after the cheat was turned on notes the value; afterwards a lower value is put
// back to the highest one seen and a higher one becomes the new highest (Atmosphère's VM keeps no state of a cheat
// between passes, so this is the host's own action)
static void nd_step(cheat_t *c) {
    unsigned w = type_width(c->type);
    if (!w || !region_ready(c, c->nd_region)) return;
    uint64_t addr = region_base(c->nd_region) + c->nd_off, cur = 0;
    if (cheat_read(c, addr, w, &cur)) return;
    if (!c->nd_have) { c->nd_max = cur; c->nd_have = 1; return; }
    if (value_less(c, w, cur, c->nd_max)) cheat_write(c, addr, w, c->nd_max);
    else c->nd_max = cur;
}

// ---------- the pass, the present hook and the idle thread ----------

static void states_save(void);

// One pass: the masters first, then the enabled cheats in file order. The VM state (registers, loop tops) is fresh each
// cheat, the reference's ResetState over its concatenated program; static registers stay. The lock is never waited for: a
// pass that arrives while a menu operation or another pass runs is simply skipped (the next frame / tick applies again).
// The master switch stops everything; safe mode holds the masters back too; a "set" cheat turns itself off after its pass
static void cheats_pass(void) {
    if (!atomic_load(&g_active) || !atomic_load(&g_master)) return;
    if (pthread_mutex_trylock(&g_lock)) return;
    if (!atomic_load(&g_master)) { pthread_mutex_unlock(&g_lock); return; }   // switched off while this pass waited for the lock
    int fired = 0;
    for (int half = 0; half < 2; half++) for (int i = 0; i < g_ncheat; i++) {
        cheat_t *c = &g_cheat[i];
        if (c->broken || c->dead || c->label) continue;
        if ((half == 0) != (c->master != 0)) continue;   // half 0 = masters, half 1 = the enabled plain cheats
        if (half == 0 && g_safe) continue;               // safe mode: the masters wait for the player too
        if (half && !c->on) continue;
        if (c->nd) { nd_step(c); continue; }
        memset(g_reg, 0, sizeof g_reg); memset(g_looptop, 0, sizeof g_looptop);   // the reference's per-pass register reset
        vm_run(c);
        if ((c->once || c->restore_once) && half) { c->on = 0; c->restore_once = 0; fired = 1; }
    }
    if (fired) states_save();
    pthread_mutex_unlock(&g_lock);
}

// Per presented frame (hle_nvn.c dump_frame): apply the cheats and note the present, so the idle thread stands down
// (brief: once per presented frame; the idle thread only when it is not presenting)
void dm_cheats_present(void) {
    atomic_store(&g_present_ns, now_ns());
    cheats_pass();
}

// The fixed ~60 Hz passes when the game is not presenting (window minimized, graphics suspended or before the first
// present): a stopped game still changes under its cheats, as on hardware where the cheat process keeps running
static void *cheat_tick_thread(void *arg) {
    (void)arg;
    while (atomic_load(&g_inited)) {
        usleep(16667);   // ~60 Hz
        if (now_ns() - atomic_load(&g_present_ns) < 250000000ull) continue;   // presenting again: the hook applies
        cheats_pass();
    }
    return NULL;
}

// ---------- the cheat states: <build>.enabled, DM_CHEATS_ON, the folder's flag files ----------

// The key of a cheat in <build>.enabled and <build>.values: its name, "Name #2" for the second entry of that name, …
static void cheat_key(const cheat_t *c, char *out, size_t n) {
    if (c->dup) snprintf(out, n, "%s #%d", c->name, c->dup + 1); else snprintf(out, n, "%s", c->name);
}


// The folder's flag files carry this game's title ID: one cheats folder may serve several games (an SD card's tree)
static void flag_file(char *out, size_t n, const char *what) { snprintf(out, n, "%s/.cheats-%s-%s", g_dir, what, g_tid); }

// The safe-mode flag: <dir>/.cheats-running-<title> exists while some cheat runs (a plain cheat on, or the masters while
// not in safe mode, with the master switch on); a clean exit removes it (dm_cheats_exit), a crash leaves it for the next
// launch. Not on iOS: an iOS app usually ends killed (swiped away, or while suspended), and the app has no cheats panel
// to leave safe mode with
static void running_update(void) {
#if TARGET_OS_IPHONE
    return;
#endif
    if (!g_dir[0] || atomic_load(&g_exiting)) return;
    int any = 0;
    for (int i = 0; i < g_ncheat && !any; i++) {
        const cheat_t *c = &g_cheat[i];
        if (c->label || c->broken) continue;
        any = c->master ? !g_safe : c->on;
    }
    char p[1100]; flag_file(p, sizeof p, "running");
    if (any && atomic_load(&g_master)) {
        FILE *f = fopen(p, "w");
        if (f) { fprintf(f, "%s\n", g_build); fclose(f); }
    } else unlink(p);
}

// Save the enabled states: one key per line, <build>.enabled in the cheats folder (masters are always on, labels never
// run, and a "set" cheat or a pending restore runs one pass only, so none of them is saved). Rewritten on every menu
// toggle, read at each load; the safe-mode flag follows the states
static void states_save(void) {
    if (!g_dir[0] || !g_build[0]) return;
    char path[1400]; snprintf(path, sizeof path, "%s/%s.enabled", g_dir, g_build);
    FILE *f = fopen(path, "w");
    if (!f) { LOG("cheats: cannot write %s (errno %d)", path, errno); return; }
    for (int i = 0; i < g_ncheat; i++) {
        const cheat_t *c = &g_cheat[i];
        if (!c->on || c->master || c->label || c->once || c->restore_once) continue;   // one-pass cheats are never saved as on
        char k[NAME_MAX + 16]; cheat_key(c, k, sizeof k); fprintf(f, "%s\n", k);
    }
    fclose(f);
    running_update();
}

// Turn on the cheats a states file names, key for key; a line that is no key ("X" written by an older version for every
// entry of that name) turns on the next entry of that name that is still off, so such a file keeps all its duplicates on.
// Returns how many it turned on, -1 when the file cannot be read
static int states_read(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) return -1;
    char line[1024]; int n = 0;
    while (fgets(line, sizeof line, f)) {
        char *save = NULL, *s = strtok_r(line, "\r\n", &save);
        if (!s) continue;
        int hit = -1;
        for (int i = 0; i < g_ncheat && hit < 0; i++) {
            cheat_t *c = &g_cheat[i];
            char k[NAME_MAX + 16]; cheat_key(c, k, sizeof k);
            if (!c->master && !c->label && !c->on && !strcmp(k, s)) hit = i;
        }
        for (int i = 0; i < g_ncheat && hit < 0; i++)
            if (!g_cheat[i].master && !g_cheat[i].label && !g_cheat[i].on && !strcmp(g_cheat[i].name, s)) hit = i;
        if (hit >= 0) { if (!g_cheat[hit].on) n++; g_cheat[hit].on = 1; }
    }
    fclose(f);
    return n;
}

// The source a meta file says it was compiled from ("" when none)
static void meta_source(const char *meta_path, char *out, size_t n) {
    out[0] = 0;
    FILE *f = fopen(meta_path, "r");
    if (!f) return;
    char line[512];
    if (fgets(line, sizeof line, f) && !strncmp(line, "# cheat_anchor.py: compiled from ", 33)) {
        char *e = strstr(line, " for build ");
        if (e) snprintf(out, n, "%.*s", (int)(e - line - 33), line + 33);
    }
    fclose(f);
}

// The newest <BID>.enabled of the folder other than this build's whose build was compiled from the same source (its
// <BID>.meta.tsv says so): a compiled file of a new build takes its toggles, the same cheats by name, and never those of
// another game or another source sharing the folder; "" when there is none
static void newest_other_enabled(char *out, size_t n) {
    out[0] = 0;
    DIR *d = opendir(g_dir);
    if (!d) return;
    struct dirent *e; time_t best = 0;
    while ((e = readdir(d))) {
        size_t L = strlen(e->d_name);
        if (L != 16 + 8 || strcasecmp(e->d_name + 16, ".enabled") || !strncasecmp(e->d_name, g_build, 16)) continue;
        char p[1400], src[256]; snprintf(p, sizeof p, "%s/%.16s.meta.tsv", g_dir, e->d_name);
        meta_source(p, src, sizeof src);
        if (!g_meta_src[0] || strcmp(src, g_meta_src)) continue;
        snprintf(p, sizeof p, "%s/%s", g_dir, e->d_name);
        struct stat st;
        if (!stat(p, &st) && st.st_mtime >= best) { best = st.st_mtime; snprintf(out, n, "%s", e->d_name); }
    }
    closedir(d);
}

// Restore the states: the saved <build>.enabled (or, for a compiled file of a build without one, the newest other
// build's), then DM_CHEATS_ON's names (name for name, case-insensitive, as the brief lets sites write the names); neither
// writes a master or a label. In safe mode the saved states wait for dm_cheats_safe_restore
static void states_load(void) {
    g_carried[0] = 0;
    if (g_dir[0] && !g_safe) {
        char path[1400]; snprintf(path, sizeof path, "%s/%s.enabled", g_dir, g_build);
        if (states_read(path) < 0 && g_have_meta) {
            char other[64]; newest_other_enabled(other, sizeof other);
            if (other[0]) {
                snprintf(path, sizeof path, "%s/%s", g_dir, other);
                if (states_read(path) >= 0) snprintf(g_carried, sizeof g_carried, "%s", other);
            }
        }
    }
    for (int k = 0; k < g_non; k++)
        for (int i = 0; i < g_ncheat; i++)
            if (!g_cheat[i].master && !g_cheat[i].label && !strcasecmp(g_cheat[i].name, g_on[k])) g_cheat[i].on = 1;
}

// ---------- typed values the panel may set ("ask") ----------

// The number base of a typed value: 16 for a "0x" prefix (after an optional sign), else 10 ("010" is ten, as
// scripts/cheat_anchor.py reads it, never C's octal)
static int value_base(const char *t) {
    while (isspace((unsigned char)*t)) t++;
    if (*t == '-' || *t == '+') t++;
    return t[0] == '0' && (t[1] == 'x' || t[1] == 'X') ? 16 : 10;
}

// Set a cheat's value from text in its meta type, within its bounds: the program words that hold it are rewritten (an
// 8-byte value: its high word, then its low word). 0 = done, -1 = refused (no ask, unparsable, out of bounds, no fit)
static int value_set_locked(cheat_t *c, const char *text) {
    unsigned w = type_width(c->type);
    if (!c->ask || !w || !c->nvw || !text || !*text) return -1;
    char *end = NULL; uint64_t raw; double d;
    errno = 0;
    if (c->type[0] == 'f') {
        d = strtod(text, &end);
        if (w == 4) { float f = (float)d; uint32_t u; memcpy(&u, &f, 4); raw = u; } else memcpy(&raw, &d, 8);
    } else if (c->type[0] == 's') {
        long long v = strtoll(text, &end, value_base(text)); d = (double)v;
        if (w < 8 && (v < -(1ll << (8 * w - 1)) || v >= (1ll << (8 * w - 1)))) return -1;
        raw = (uint64_t)v & width_mask(w);
    } else {
        if (strchr(text, '-')) return -1;
        unsigned long long v = strtoull(text, &end, value_base(text)); d = (double)v;
        if (w < 8 && v > width_mask(w)) return -1;
        raw = v;
    }
    if (errno || end == text || (end && *end && !isspace((unsigned char)*end))) return -1;
    if ((c->has_min && d < c->vmin) || (c->has_max && d > c->vmax)) return -1;
    int per = w == 8 ? 2 : 1;
    for (int k = 0; k + per <= c->nvw; k += per) {
        if (per == 2) { c->ins[c->vw[k]] = (uint32_t)(raw >> 32); c->ins[c->vw[k + 1]] = (uint32_t)raw; }
        else c->ins[c->vw[k]] = (uint32_t)raw;
    }
    return 0;
}

// The current value of an ask cheat as text in its type ("" when it takes none)
static void value_get(const cheat_t *c, char *out, size_t n) {
    out[0] = 0;
    unsigned w = type_width(c->type);
    if (!c->ask || !w || !c->nvw) return;
    uint64_t raw = w == 8 && c->nvw >= 2 ? ((uint64_t)c->ins[c->vw[0]] << 32) | c->ins[c->vw[1]] : c->ins[c->vw[0]] & width_mask(w);
    char k = c->type[0];
    if (k == 'f' && w == 4) { uint32_t u = (uint32_t)raw; float f; memcpy(&f, &u, 4); snprintf(out, n, "%g", f); }
    else if (k == 'f') { double v; memcpy(&v, &raw, 8); snprintf(out, n, "%g", v); }
    else if (k == 's') { int sh = 64 - 8 * (int)w; snprintf(out, n, "%lld", (long long)((int64_t)(raw << sh) >> sh)); }
    else snprintf(out, n, "%llu", (unsigned long long)raw);
}

// Save the panel's values: <build>.values, one "key<TAB>value" line per ask cheat
static void values_save(void) {
    if (!g_dir[0] || !g_build[0]) return;
    char path[1400]; snprintf(path, sizeof path, "%s/%s.values", g_dir, g_build);
    FILE *f = fopen(path, "w");
    if (!f) { LOG("cheats: cannot write %s (errno %d)", path, errno); return; }
    for (int i = 0; i < g_ncheat; i++) {
        if (!g_cheat[i].ask) continue;
        char k[NAME_MAX + 16], v[64]; cheat_key(&g_cheat[i], k, sizeof k); value_get(&g_cheat[i], v, sizeof v);
        fprintf(f, "%s\t%s\n", k, v);
    }
    fclose(f);
}

// Apply <build>.values (a value that no longer fits its bounds keeps the file's own)
static void values_load(void) {
    if (!g_dir[0]) return;
    char path[1400]; snprintf(path, sizeof path, "%s/%s.values", g_dir, g_build);
    FILE *f = fopen(path, "r");
    if (!f) return;
    char line[1024];
    while (fgets(line, sizeof line, f)) {
        char *tab = strchr(line, '\t');
        if (!tab) continue;
        char *save = NULL;
        *tab = 0; char *v = strtok_r(tab + 1, "\r\n", &save);
        for (int i = 0; i < g_ncheat && v; i++) {
            char k[NAME_MAX + 16]; cheat_key(&g_cheat[i], k, sizeof k);
            if (!strcmp(k, line)) { value_set_locked(&g_cheat[i], v); break; }
        }
    }
    fclose(f);
}

// ---------- loading: the folder, the build's file, the parse, the meta file ----------

// The folders scanned, in the brief's order: the flat folder, the Atmosphère tree under it
// (atmosphere/contents/<tid>/cheats) and the tree with the folder itself as the "atmosphere" half (contents/<tid>/cheats)
static int scan_dirs(char out[3][1024]) {
    if (!g_dir[0] || !g_tid[0]) return 0;
    snprintf(out[0], 1024, "%s", g_dir);
    snprintf(out[1], 1024, "%s/atmosphere/contents/%s/cheats", g_dir, g_tid);
    snprintf(out[2], 1024, "%s/contents/%s/cheats", g_dir, g_tid);
    return 3;
}

// Does the file name hold exactly this build ID (any case), as the atmosphere loader names its cheat files?
static int name_is_build(const char *name, const char *build) {
    for (int k = 0; k < 16; k++) {
        char a = name[k], b = build[k];
        if (!a) return 0;
        a = (char)tolower((unsigned char)a); b = (char)tolower((unsigned char)b);
        if (a != b) return 0;
    }
    return (int)strlen(name) >= 16 && (name[16] == '.' || !name[16]);
}

// The first 16 characters as a hex build ID (for the other-build list)? "another version of the game" needs a real
// build ID name, so hunks like "readme.txt" do not show up as builds
static int name_hex16(const char *name) {
    if (strlen(name) < 16) return 0;
    for (int k = 0; k < 16; k++) {
        char a = (char)tolower((unsigned char)name[k]);
        if (!((a >= '0' && a <= '9') || (a >= 'a' && a <= 'f'))) return 0;
    }
    return 1;
}

static char g_cand[CAND_MAX][2048]; static int g_ncand;

// Collect the .txt files of one folder (case-insensitive suffix, .enabled ignored), deduped by path
static void collect_dir(const char *dir_) {
    DIR *d = opendir(dir_);
    if (!d) return;
    struct dirent *e;
    while ((e = readdir(d))) {
        size_t n = strlen(e->d_name);
        if (n < 5 || strcasecmp(e->d_name + n - 4, ".txt")) continue;
        if (g_ncand >= CAND_MAX) break;
        char *p = g_cand[g_ncand];
        snprintf(p, 2048, "%s/%s", dir_, e->d_name);
        int dup = 0;
        for (int i = 0; i < g_ncand; i++) if (!strcmp(g_cand[i], p)) { dup = 1; break; }
        if (!dup) g_ncand++;
    }
    closedir(d);
}

// The whole file, with a header glued to a code word ("00000008[Next]": a whole 8-hex-digit word at the start of the line
// or after a space) moved to a piece of its own (a '\v' break, which parse_file splits on without counting a line); NULL
// when it cannot be read or is larger than FILE_MAX (no cheat file is). The caller frees it
static char *read_text(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    char *raw = malloc(FILE_MAX + 2);
    size_t n = raw ? fread(raw, 1, FILE_MAX + 1, f) : 0;
    fclose(f);
    if (!raw) return NULL;
    if (n > FILE_MAX) { LOG("[RED] cheats: %s is larger than %u bytes: not a cheat file", path, FILE_MAX); free(raw); errno = EFBIG; return NULL; }
    raw[n] = 0;
    char *out = malloc(2 * n + 1);
    if (!out) { free(raw); return NULL; }
    size_t o = 0;
    for (size_t i = 0; i < n; i++) {
        if ((raw[i] == '[' || raw[i] == '{') && i >= 8) {   // a header right after a whole code word
            int word = 1;
            for (size_t k = i - 8; k < i && word; k++) word = isxdigit((unsigned char)raw[k]) != 0;
            if (word && (i == 8 || raw[i - 9] == ' ' || raw[i - 9] == '\t' || raw[i - 9] == '\n' || raw[i - 9] == '\r')) { out[o++] = '\v'; g_glued++; }
        }
        out[o++] = raw[i];
    }
    out[o] = 0;
    free(raw);
    return out;
}

// EdiZon's section markers: [--SectionStart:Name--] (1) / [--SectionEnd:Name--] (2), the name copied out; 0 otherwise
static int section_marker(const char *name, char *sec, size_t n) {
    size_t L = strlen(name);
    if (L < 4 || strcmp(name + L - 2, "--")) return 0;
    int kind = !strncmp(name, "--SectionStart:", 15) ? 1 : !strncmp(name, "--SectionEnd:", 13) ? 2 : 0;
    if (!kind) return 0;
    size_t s = kind == 1 ? 15 : 13;
    snprintf(sec, n, "%.*s", (int)(L - 2 - s), name + s);
    return kind;
}

// Parse the file into the cheats array; lines other than [Name] / {Name} headers and 8-hex-digit code words
// separated by spaces are ignored (the brief), with one [RED] line for a line whose words are code-like but not valid.
// An entry without code words is a label (its name only: credits, or a section marker that sets the section of the
// entries after it); every entry notes how many earlier entries carry its name (dup, the key of a duplicate)
static void parse_file(const char *path) {
    char *text = read_text(path);
    if (!text) { LOG("[RED] cheats: cannot read %s (errno %d)", path, errno); return; }
    cheat_t *cur = NULL;
    int lineno = 1, warned = 0;   // the file line of the next piece
    char section[NAME_MAX] = "";
    static uint32_t got[INS_MAX];   // one line's words (static: 32 KB, parse_file runs under g_lock only)
    for (char *line = text, *next; line; line = next) {
        // one piece: a file line, or part of one when a glued header was split off with '\v'
        char *e = line + strcspn(line, "\n\v");
        char sep = *e;
        next = sep ? e + 1 : NULL;
        *e = 0;
        int ln = lineno;            // the file line this piece is on, for the [RED] lines
        if (sep == '\n') lineno++;
        char *p = line;
        while (*p == ' ' || *p == '\t') p++;
        char end = 0;
        if (*p == '[') end = ']';
        else if (*p == '{') end = '}';
        if (end) {   // a header starts a new cheat; the name is what lies inside
            char *q = strchr(p, end);
            size_t nl = q && q > p ? (size_t)(q - p - 1) : 0;
            if (nl == 0 || g_ncheat >= CHEAT_MAX) {
                if (g_ncheat >= CHEAT_MAX && !warned++) LOG("[RED] cheats: more than %d cheats in %s, the rest is skipped", CHEAT_MAX, path);
                cur = NULL;
                continue;
            }
            cur = &g_cheat[g_ncheat++];
            memset(cur, 0, sizeof *cur);
            cur->pair = -1;
            // the name keeps NAME_MAX - 1 characters: a shorter cut once let two long-named cheats share a line in <build>.enabled
            snprintf(cur->name, NAME_MAX, "%.*s", (int)(nl > 127 ? 127 : nl), p + 1);
            cur->master = end == '}';
            cur->on = cur->master;
            char sec[NAME_MAX];
            int mark = section_marker(cur->name, sec, sizeof sec);
            if (mark == 1) snprintf(section, sizeof section, "%s", sec);
            if (mark) cur->sec_mark = (uint8_t)mark;
            snprintf(cur->section, NAME_MAX, "%s", mark == 1 ? sec : section);
            if (mark == 2) section[0] = 0;
            for (int i = 0; i < g_ncheat - 1; i++) if (!strcmp(g_cheat[i].name, cur->name)) cur->dup++;
            p = q + 1;                 // dmnt reads on after the header: code words may follow on the same line
            while (*p == ' ' || *p == '\t' || *p == '\r') p++;
            if (!*p) continue;
        }
        if (!cur) continue;   // words before any [Name] / {Name} header belong to nothing: the line is ignored (site files carry prose)
        // the words of the line: whole tokens of exactly 8 hex digits; anything else makes the line prose
        int ngot = 0, bad = 0;
        const char *badt = "";   // the token that is not a word, named on the [RED] line
        for (char *s2 = NULL, *t = strtok_r(p, " \t\r", &s2); t; t = strtok_r(NULL, " \t\r", &s2)) {
            if (strlen(t) != 8) { bad = 1; badt = t; break; }
            uint32_t w = 0;
            for (int k = 0; k < 8; k++) {
                char a = (char)tolower((unsigned char)t[k]);
                unsigned d = a >= '0' && a <= '9' ? (unsigned)(a - '0') : a >= 'a' && a <= 'f' ? (unsigned)(a - 'a' + 10) : 16;
                if (d == 16) { bad = 1; badt = t; break; }
                w = w << 4 | d;
            }
            if (bad) break;
            if (ngot < INS_MAX) got[ngot++] = w;
            else { LOG("[RED] cheat \"%s\": line %d has more than %d code words, the rest of the line is ignored", cur->name, ln, INS_MAX); break; }
        }
        if (!ngot && !bad) continue;   // only whitespace
        if (bad && !ngot) {   // the file format ignores the line (the brief's "other lines"): prose, once warned
            if (!g_junk++) g_junk_line = ln;
            if (!cur->junk_line) cur->junk_line = ln;
            if (!warned++) LOG("[RED] cheats: %s line %d is not code words and is ignored", path, ln);
            continue;
        }
        if (bad) {
            // words would be dropped from a line that held them: the dropped token may carry an instruction of its
            // own (a vanished begin or end leaves the body running every frame unconditionally), so the cheat stays
            // off entirely instead of silently running a fragment of itself; once per cheat, with the token named
            if (!cur->broken) {
                cur->broken = 1; snprintf(cur->why, sizeof cur->why, " (malformed line %d)", ln);
                LOG("[RED] cheats: %s: \"%s\" line %d mixes code words with \"%s\", the cheat stays off", path, cur->name, ln, badt);
            }
            continue;
        }
        if (cur->nins + ngot > INS_MAX) { LOG("[RED] cheat \"%s\": over %d code words, skipped", cur->name, INS_MAX); continue; }
        memcpy(cur->ins + cur->nins, got, sizeof(uint32_t) * (size_t)ngot);
        cur->nins += ngot;
    }
    free(text);
    // The verdict per cheat: no code words at all is a label (the meta file may still make it a host action), unless lines
// under it were dropped as prose (then it is broken, with the first such line named); anything
    // else is decoded word by word, and one instruction the VM does not run (unsupported opcode, region, width,
    // condition) or the words ending inside a field turns the whole cheat off, shown in the menu with the reason, never run
    for (int i = 0; i < g_ncheat; i++) {
        cheat_t *c = &g_cheat[i];
        if (c->broken) continue;   // already off with its own reason (a malformed line): the decode would overwrite why
        if (c->nins == 0 && c->junk_line) {   // its lines were all prose: a broken cheat (a typo), not a label
            c->broken = 1; snprintf(c->why, sizeof c->why, " (no code words: line %d is not code)", c->junk_line); continue;
        }
        if (c->nins == 0) { c->label = 1; c->on = 0; continue; }
        for (int a = 0; a < c->nins;) {
            ins_t in;
            int len = ins_dec(c, c->ins + a, c->nins - a, &in);
            if (len <= 0) break;   // the reason is already in c->why and c->broken is set
            a += len;
        }
    }
}

// Split a TSV line into at most max fields in place (empty fields kept); returns the count
static int tsv_split(char *line, char **f, int max) {
    int n = 0;
    char *s = line;
    while (n < max) {
        f[n++] = s;
        char *t = strchr(s, '\t');
        if (!t) break;
        *t = 0; s = t + 1;
    }
    char *e = f[n - 1] + strcspn(f[n - 1], "\r\n"); *e = 0;
    return n;
}

// The display version a meta file's header names for a build ("# build <BID> <version>"), "" when none
static void meta_version(const char *meta_path, const char *bid, char *out, size_t n) {
    out[0] = 0;
    FILE *f = fopen(meta_path, "r");
    if (!f) return;
    char line[512];
    while (fgets(line, sizeof line, f) && line[0] == '#') {
        if (strncmp(line, "# build ", 8) || strncasecmp(line + 8, bid, 16) || line[24] != ' ') continue;
        snprintf(out, n, "%s", line + 25); out[strcspn(out, "\r\n")] = 0;
    }
    fclose(f);
}

// Is program word k of a cheat a value field of its instruction (the value of 0 / 1 / 4 / 6 / 7, C0's static value)?
// Decodes with a scratch cheat, so the cheat itself is never touched
static int value_word(const cheat_t *c, int k) {
    static cheat_t probe;   // the decoder's scratch (it writes why / broken on a failure); callers hold g_lock
    for (int a = 0; a < c->nins;) {
        ins_t in;
        int len = ins_dec(&probe, c->ins + a, c->nins - a, &in);
        if (len <= 0) return 0;
        int first = in.op == 0 || in.op == 1 ? a + 2 : in.op == 4 || in.op == 6 || in.op == 7 ? a + 1 : in.op == 0xC0 && in.o == 4 ? a + 1 : -1;
        if (first >= 0 && k >= first && k < a + len) return 1;
        a += len;
    }
    return 0;
}

// <txt>.meta.tsv: the companion scripts/cheat_anchor.py writes beside a compiled <build>.txt. Its rows go to the
// entries of the same name in file order (a duplicate name's rows to its entries in turn); "unresolved" rows (cheats the
// compiler left out) are listed for the panel. Columns are read by their header names
static void meta_load(const char *txt_path) {
    char path[2100];
    size_t L = strlen(txt_path);
    if (L < 4 || strcasecmp(txt_path + L - 4, ".txt")) return;
    snprintf(path, sizeof path, "%.*s.meta.tsv", (int)(L - 4), txt_path);
    FILE *f = fopen(path, "r");
    if (!f) return;
    g_have_meta = 1;
    meta_source(path, g_meta_src, sizeof g_meta_src);
    enum { NAME, KIND, SECTION, TYPE, ACTION, ASK, VWORDS, ONCE, PAIR, RESOLVED, NOTE, ADDRESS, NCOL };
    static const char *cols[NCOL] = {"name", "kind", "section", "type", "action", "ask", "value_words", "once", "pair", "resolved", "note", "address"};
    int at[NCOL]; for (int k = 0; k < NCOL; k++) at[k] = -1;
    char line[4096]; int cursor = 0, head = 0;
    while (fgets(line, sizeof line, f)) {
        if (line[0] == '#') {
            if (!g_version[0] && !strncmp(line, "# build ", 8) && !strncasecmp(line + 8, g_build, 16) && line[24] == ' ') {
                snprintf(g_version, sizeof g_version, "%s", line + 25); g_version[strcspn(g_version, "\r\n")] = 0;
            }
            continue;
        }
        char *fld[24]; int nf = tsv_split(line, fld, 24);
        if (!head) {   // the header row: column names to indexes
            head = 1;
            for (int i = 0; i < nf; i++) for (int k = 0; k < NCOL; k++) if (!strcmp(fld[i], cols[k])) at[k] = i;
            if (at[NAME] < 0) break;
            continue;
        }
        #define COL(k) (at[k] >= 0 && at[k] < nf ? fld[at[k]] : "")
        const char *name = COL(NAME), *kind = COL(KIND);
        if (!strcmp(kind, "unresolved")) {
            if (g_nskip < SKIP_MAX) { snprintf(g_skip_name[g_nskip], NAME_MAX, "%s", name); snprintf(g_skip_why[g_nskip], 160, "%s", COL(NOTE)); g_nskip++; }
            continue;
        }
        int j = cursor;
        while (j < g_ncheat && strcmp(g_cheat[j].name, name)) j++;
        if (j >= g_ncheat) continue;   // no entry of that name after the previous one: the row is ignored
        cursor = j + 1;
        cheat_t *c = &g_cheat[j];
        if (COL(SECTION)[0] && !c->section[0]) snprintf(c->section, NAME_MAX, "%s", COL(SECTION));
        snprintf(c->type, sizeof c->type, "%s", COL(TYPE));
        if (!strcmp(COL(ONCE), "1")) c->once = 1;
        if (!strcmp(kind, "patch-off")) c->pair_off = 1;
        snprintf(c->pairname, NAME_MAX, "%s", COL(PAIR));
        if (strstr(COL(RESOLVED), "weak")) c->weak = 1;
        snprintf(c->note, sizeof c->note, "%s%s%s", COL(RESOLVED), COL(RESOLVED)[0] && COL(NOTE)[0] ? "; " : "", COL(NOTE));
        if (COL(ASK)[0]) {   // "min..max", either side may be empty
            const char *a = COL(ASK), *dots = strstr(a, "..");
            c->ask = 1;
            if (dots && dots > a) { c->vmin = strtod(a, NULL); c->has_min = 1; }
            if (dots && dots[2]) { c->vmax = strtod(dots + 2, NULL); c->has_max = 1; }
            for (char *s = (char *)COL(VWORDS), *e; *s && c->nvw < VW_MAX; s = *e ? e + 1 : e) {
                long v = strtol(s, &e, 10);
                if (e == s) break;
                if (v >= 0 && v < c->nins) c->vw[c->nvw++] = (int)v;
            }
            // the indexes must be value words of the program's own instructions, in whole values (an 8-byte value is two
            // words): a value set may never rewrite an opcode word behind the load-time verdict
            unsigned w = type_width(c->type);
            if (!w || !c->nvw || c->nvw % (w == 8 ? 2 : 1) || c->broken) c->ask = 0;
            for (int k = 0; k < c->nvw && c->ask; k++) if (!value_word(c, c->vw[k])) c->ask = 0;
        }
        if (!strcmp(COL(ACTION), "never-decrease") && c->nins == 0) {   // "region:0xOFFSET" of a typed address
            const char *a = COL(ADDRESS), *colon = strchr(a, ':');
            if (colon && type_width(c->type)) {
                c->nd_region = (uint8_t)atoi(a); c->nd_off = strtoull(colon + 1, NULL, 0);
                if (c->nd_region <= 1) { c->nd = 1; c->label = 0; }
            }
        }
        #undef COL
    }
    fclose(f);
}

// "X - on" / "X - off" (also "X on", "X: off", "X (off)", …): the base name and which half, 1 when the name has the form
static int onoff_split(const char *name, char *base, size_t n, int *is_off) {
    size_t e = strlen(name);
    while (e && isspace((unsigned char)name[e - 1])) e--;
    if (e && (name[e - 1] == ')' || name[e - 1] == ']')) e--;
    int off;
    if (e >= 3 && !strncasecmp(name + e - 3, "off", 3)) { off = 1; e -= 3; }
    else if (e >= 2 && !strncasecmp(name + e - 2, "on", 2)) { off = 0; e -= 2; }
    else return 0;
    size_t s = e; int sep = 0;
    while (s && strchr(" -:_([", name[s - 1])) { s--; sep = 1; }
    if (!sep || !s) return 0;
    snprintf(base, n, "%.*s", (int)s, name);
    *is_off = off;
    return 1;
}

// Link on / off pairs: the meta file's pair names first, then the naming convention for files without one; both halves
// must be plain runnable cheats (a master runs whatever its toggle says, so it can never be half of a switch)
static void pairs_link(void) {
    for (int i = 0; i < g_ncheat; i++) {
        cheat_t *c = &g_cheat[i];
        if (!c->pairname[0] || c->pair >= 0 || c->master || c->label || c->nd || c->broken) continue;
        for (int j = 0; j < g_ncheat; j++) {
            cheat_t *o = &g_cheat[j];
            if (j == i || o->pair >= 0 || o->master || o->label || o->nd || o->broken || strcmp(o->name, c->pairname)) continue;
            c->pair = j; o->pair = i; break;
        }
    }
    for (int i = 0; i < g_ncheat; i++) {
        cheat_t *a = &g_cheat[i]; char ba[NAME_MAX]; int offa;
        if (a->pair >= 0 || a->master || a->label || a->nd || !onoff_split(a->name, ba, sizeof ba, &offa)) continue;
        for (int j = i + 1; j < g_ncheat; j++) {
            cheat_t *b = &g_cheat[j]; char bb[NAME_MAX]; int offb;
            if (b->pair >= 0 || b->master || b->label || b->nd || !onoff_split(b->name, bb, sizeof bb, &offb)) continue;
            if (offa == offb || strcasecmp(ba, bb)) continue;
            a->pair = j; b->pair = i; a->pair_off = (uint8_t)offa; b->pair_off = (uint8_t)offb;
            break;
        }
    }
}

// The load report (dm_cheats_report, and the log): counts, duplicate names, ignored lines, where the states came from,
// the compiler's left-outs, and Atmosphère's limits (a Switch refuses past them; this host takes more)
static void report_build(void) {
    char *r = g_report; size_t n = sizeof g_report, o = 0;
    #define ADD(...) do { if (o < n) o += (size_t)snprintf(r + o, n - o, __VA_ARGS__); } while (0)
    int cheats = 0, on = 0, bad = 0, labels = 0, sections = 0, masters = 0, enabled_words = 0, big = 0;
    for (int i = 0; i < g_ncheat; i++) {
        const cheat_t *c = &g_cheat[i];
        if (c->label) { labels++; sections += c->sec_mark == 1; continue; }
        cheats++; masters += c->master; bad += c->broken;
        if ((c->on || c->master) && !c->broken) { on += !c->master; enabled_words += c->nins; }
        if (c->nins > ATM_WORDS) big++;
    }
    r[0] = 0;
    ADD("Build %s%s%s%s: %d cheats (%d on, %d master, %d broken)", g_build, g_version[0] ? " (" : "", g_version, g_version[0] ? ")" : "", cheats, on, masters, bad);
    if (labels) ADD(", %d labels (%d sections)", labels, sections);
    ADD("\n");
    int dups = 0;
    for (int i = 0; i < g_ncheat; i++) if (g_cheat[i].dup == 1 && !g_cheat[i].label) { if (!dups++) ADD("Duplicate names (saved as \"Name #2\", …):"); ADD(" \"%s\"", g_cheat[i].name); }
    if (dups) ADD("\n");
    if (g_junk) ADD("%d lines that are not code words were ignored (the first: line %d)\n", g_junk, g_junk_line);
    if (g_glued) ADD("%d headers glued to a code line were split off\n", g_glued);
    if (g_carried[0]) ADD("Toggles carried over from %s (no %s.enabled yet)\n", g_carried, g_build);
    if (g_safe) ADD("Safe mode: the last run ended without a clean exit while cheats were on; every cheat starts off\n");
    if (!atomic_load(&g_master)) ADD("The master switch is off: no cheat runs\n");
    if (g_nskip) ADD("%d cheats were left out when this file was compiled\n", g_nskip);
    if (cheats > ATM_CHEATS || big || enabled_words > ATM_PROGRAM)
        ADD("Over Atmosphère's limits (a Switch refuses them): %d cheats (0x80), %d cheats over 0x100 words, %d words enabled (0x400)\n", cheats, big, enabled_words);
    #undef ADD
}

// This build's display version from the profile's build rows (by the whole main build ID), as GetDisplayVersion answers it
static void profile_version(void) {
#ifdef DM_GAME_DISPLAY_VERSIONS
    static const struct { const char *build, *ver; } k[] = {DM_GAME_DISPLAY_VERSIONS};
    const char *bid = dm_main_build();
    for (unsigned j = 0; j < sizeof k / sizeof *k; j++) if (!strcasecmp(bid, k[j].build)) snprintf(g_version, sizeof g_version, "%s", k[j].ver);
#endif
}

// The anchored sources (*.cheats.toml) in the folder, for the panel's "compile them for this build" hint
static void sources_scan(void) {
    g_nsrc = 0;
    DIR *d = g_dir[0] ? opendir(g_dir) : NULL;
    if (!d) return;
    struct dirent *e;
    while ((e = readdir(d)) && g_nsrc < SRC_MAX) {
        size_t L = strlen(e->d_name);
        if (L > 12 && !strcasecmp(e->d_name + L - 12, ".cheats.toml")) snprintf(g_src[g_nsrc++], sizeof g_src[0], "%s", e->d_name);
    }
    closedir(d);
}

// (Re)load: choose the file, note the other builds, parse, read the meta file and the values, link pairs, restore the
// states, build the report. Called at init and from "Reload cheats" (safe mode and the master switch stay as they are)
static void load_all(void) {
    g_ncheat = 0; g_ncand = 0; g_nothers = 0; g_path[0] = 0; g_nskip = 0; g_have_meta = 0;
    g_junk = g_junk_line = g_glued = 0; g_carried[0] = 0; g_version[0] = 0; g_meta_src[0] = 0;
    memset(g_static, 0, sizeof g_static);   // the reference clears its static registers when it loads cheats
    atomic_store(&g_active, 0);
    profile_version();
    sources_scan();
    char dirs[3][1024]; int nd = scan_dirs(dirs);
    for (int i = 0; i < nd; i++) collect_dir(dirs[i]);
    if (!g_build[0]) { LOG("[RED] cheats: the main NSO has no build ID, so no file can be picked from %s", g_dir); return; }
    int pick = -1, other = 0;   // pick = the matching candidate; other = when a non-matching one is used by DM_CHEATS_ANY_BUILD
    for (int i = 0; i < g_ncand; i++) {   // the whole list is walked: the build's file may lie after an "another version" one
        const char *nm = strrchr(g_cand[i], '/') + 1;
        int hex = name_hex16(nm);
        if (!hex) continue;
        if (name_is_build(nm, g_build)) {
            if (pick < 0) pick = i;   // the first matching candidate wins (the flat folder, then the Atmosphere tree)
            continue;   // keep walking: the other builds get collected below either way
        }
        // the other versions of the game (max OTHER_MAX, the menu shows them disabled), with their versions when a meta file names them
        int dup = 0;
        for (int k = 0; k < g_nothers; k++) if (!strncasecmp(g_others[k], nm, 16)) { dup = 1; break; }
        if (!dup && g_nothers < OTHER_MAX) {
            snprintf(g_others[g_nothers], 17, "%s", nm);
            char mp[2100]; snprintf(mp, sizeof mp, "%.*s.meta.tsv", (int)(strlen(g_cand[i]) - 4), g_cand[i]);
            meta_version(mp, g_others[g_nothers], g_other_ver[g_nothers], sizeof g_other_ver[0]);
            g_nothers++;
        }
    }
    if (pick < 0 && !(g_any && g_ncand == 1)) {
        LOG("cheats: %s: no file for build %s", g_dir, g_build);
        if (g_nothers && atomic_load(&g_dbg)) {   // the menu's "another version" rows, this file's context
            char list[OTHER_MAX * 18]; list[0] = 0;
            for (int i = 0; i < g_nothers; i++) { strlcat(list, " ", sizeof list); strlcat(list, g_others[i], sizeof list); }
            LOG("cheats: %s: %d .txt of other builds in the folder:%s", g_dir, g_nothers, list);
        }
        report_build();
        return;
    }
    if (pick < 0) { pick = 0; other = 1; }   // DM_CHEATS_ANY_BUILD and a single non-matching file: load it
    g_nothers = 0;   // a file is loaded (this build's own, or DM_CHEATS_ANY_BUILD's): no "another version" rows
    snprintf(g_path, sizeof g_path, "%s", g_cand[pick]);
    // The writable alias of main is mapped once a cheat file is actually picked, not at init merely because DM_ROOT is
    // set: a run without cheats would otherwise always map a second image of main and log a line for it. At init the
    // pick happens before the guest starts; a later "Reload cheats" retries only when no alias mapped the first time
    if (g_main_mod && !g_alias) {
        alias_setup();
        LOG("cheats: writable alias of main %s", g_alias ? "mapped" : "not mapped (mprotect toggle fallback)");
    }
    parse_file(g_path);
    meta_load(g_path);
    pairs_link();
    values_load();
    states_load();
    // the summary: masters are always on, a broken / empty cheat never runs, the rest keep the menu's saved state
    int on = 0, bad = 0, masters = 0, labels = 0;
    for (int i = 0; i < g_ncheat; i++) {
        if (g_cheat[i].label) { labels++; continue; }
        if (g_cheat[i].master) masters++;
        if (g_cheat[i].broken) bad++;
        else if (!g_cheat[i].master && g_cheat[i].on) on++;
    }
    if (other) LOG("[RED] cheats: no file for build %s, loading %s of another build on DM_CHEATS_ANY_BUILD: its addresses may be wrong", g_build, g_cand[pick]);
    LOG("cheats: %s: build %s: %d cheats (%d master, %d on, %d broken, %d runnable)%s", g_path, g_build, g_ncheat - labels, masters, on, bad, g_ncheat - labels - bad,
        g_have_meta ? ", with its meta file" : "");
    report_build();
    atomic_store(&g_active, g_ncheat > labels);
    running_update();
}

// The folder's flag files of this game, read once at init: .cheats-off-<title> (the master switch) and
// .cheats-running-<title> (left behind by a run that did not end cleanly while cheats were on: safe mode for this launch)
static void folder_flags(void) {
    if (!g_dir[0]) return;
    char p[1100];
    flag_file(p, sizeof p, "off");
    atomic_store(&g_master, access(p, F_OK) != 0);
#if !TARGET_OS_IPHONE   // iOS keeps no safe mode (running_update)
    flag_file(p, sizeof p, "running");
    g_safe = access(p, F_OK) == 0;
#endif
    if (g_safe) LOG("[RED] cheats: the last run ended without a clean exit while cheats were on: every cheat starts off (the Cheats panel restores them)");
}

// Read the switches, find the game's file, load it, and start the idle apply thread. Called after load_modules
// (main.c host_preload): the build ID to pick the file by comes from the modules them
void dm_cheats_init(void) {
    atomic_store(&g_dbg, !!getenv("DM_CHEATS_DEBUG"));
    const char *e = getenv("DM_CHEATS_ANY_BUILD"); g_any = e && *e && atoi(e) != 0;
    e = getenv("DM_CHEATS");
    if (e && *e) snprintf(g_dir, sizeof g_dir, "%s", e);
    else { e = getenv("DM_ROOT"); if (e && *e) snprintf(g_dir, sizeof g_dir, "%s/cheats", e); }
    snprintf(g_tid, sizeof g_tid, "%016llX", (unsigned long long)DM_GAME_PROGRAM_ID);
    // g_build: the main NSO's first 16 hex digits, upper case like the menu and the brief state them; the candidate
    // match itself is case-insensitive (name_is_build lower-cases both sides)
    const char *bid = dm_main_build();
    if (strlen(bid) >= 16) {
        for (int k = 0; k < 16; k++) g_build[k] = (char)toupper((unsigned char)bid[k]);
        g_build[16] = 0;
    }
    e = getenv("DM_CHEATS_ON");
    if (e && *e) {   // one-off names turned on at launch, split on ','; the saves' own <build>.enabled states stay too
        char *dup = strdup(e), *s = dup;
        while (s && g_non < 16) {
            char *t = strchr(s, ',');
            if (t) *t = 0;
            if (*s) snprintf(g_on[g_non++], NAME_MAX, "%s", s);
            s = t ? t + 1 : NULL;
        }
        free(dup);
    }
    if (!g_dir[0]) { LOG("cheats: off (neither DM_CHEATS nor DM_ROOT is set)"); }
    else {   // for the main module the pass needs its base: the loader's g_mod tables them by name
        for (int i = 0; i < g_nmod; i++) if (!strcmp(g_mod[i].name, "main") && !g_mod[i].nro) { g_main_mod = &g_mod[i]; break; }
        folder_flags();
        if (g_main_mod) { pthread_mutex_lock(&g_lock); load_all(); pthread_mutex_unlock(&g_lock); }   // load_all maps the writable alias once a file is picked
        atexit(dm_cheats_exit);   // exit() paths (⌘Q, closing the window); dm_host_exit's _exit calls it itself
    }
    atomic_store(&g_inited, 1);
    pthread_t th; pthread_attr_t a; pthread_attr_init(&a); pthread_attr_setdetachstate(&a, PTHREAD_CREATE_DETACHED);
    // The idle thread always runs (it stands down while the presents are recent, and a later "Reload cheats" that
    // brings cheats in must also get its idle passes)
    if (pthread_create(&th, &a, cheat_tick_thread, NULL)) LOG("[RED] cheats: cannot start the ~60 Hz apply thread (errno %d), only presents apply", errno);
    pthread_attr_destroy(&a);
}

// A clean exit: no cheat runs any more, so the safe-mode flag goes (atexit, and dm_host_exit before its _exit)
void dm_cheats_exit(void) {
    atomic_store(&g_exiting, 1);   // a pass still running on another thread must not write the flag back
    if (!g_dir[0]) return;
    char p[1100]; flag_file(p, sizeof p, "running");
    unlink(p);
}

// ---------- the Mac cheats menu and panel (callers: front_mac.m; nothing else uses these) ----------
// Cheap accessors read straight from the shared state: the list itself is rebuilt only from the main thread (this
// menu's own actions, and init on the Mac's main thread), and a VM pass mutates only its own cheat's dead / why flags,
// the on / restore_once flags of a one-pass cheat, the never-decrease state, and the files <build>.enabled and the safe-mode
// flag when a one-pass cheat fired; the worst-case tear shows as one stale row in a row rebuilt in that instant. Each
// accessor's meaning is in dm.h

int dm_cheats_found(void) { return atomic_load(&g_active) || g_ncheat > 0; }   // a file, of this build or another

int dm_cheats_ncheats(void) { return g_ncheat; }

const char *dm_cheats_build(void) { return g_build; }   // static after init

const char *dm_cheats_dir_path(void) { return g_dir; }   // "" when neither DM_CHEATS nor DM_ROOT is set

int dm_cheats_nothers(void) { return g_nothers; }

const char *dm_cheats_other(int i) { return i >= 0 && i < g_nothers ? g_others[i] : ""; }

const char *dm_cheats_other_version(int i) { return i >= 0 && i < g_nothers ? g_other_ver[i] : ""; }

const char *dm_cheats_version(void) { return g_version; }

const char *dm_cheat_name_at(int i) { return i >= 0 && i < g_ncheat ? g_cheat[i].name : ""; }

const char *dm_cheat_why_at(int i) { return i >= 0 && i < g_ncheat ? g_cheat[i].why : ""; }

const char *dm_cheat_section_at(int i) { return i >= 0 && i < g_ncheat ? g_cheat[i].section : ""; }

const char *dm_cheat_note_at(int i) { return i >= 0 && i < g_ncheat ? g_cheat[i].note : ""; }

const char *dm_cheat_type_at(int i) { return i >= 0 && i < g_ncheat ? g_cheat[i].type : ""; }

int dm_cheat_pair_at(int i) { return i >= 0 && i < g_ncheat ? g_cheat[i].pair : -1; }

// The row's kind, for the menu's builder: 0 = a plain cheat (click toggles), 1 = master (always on, no click),
// 2 = broken / off (disabled), 3 = a label (credits, a section marker: no checkbox). The checkmark itself: dm_cheat_on_at
int dm_cheat_kind_at(int i) {
    if (i < 0 || i >= g_ncheat) return 2;
    const cheat_t *c = &g_cheat[i];
    return c->label ? 3 : c->broken || c->dead ? 2 : c->master ? 1 : 0;
}

// The row's DM_CHEAT_* flags (dm.h)
int dm_cheat_flags_at(int i) {
    if (i < 0 || i >= g_ncheat) return 0;
    const cheat_t *c = &g_cheat[i];
    return (c->label ? DM_CHEAT_LABEL : 0) | (c->sec_mark == 1 ? DM_CHEAT_SECTION_START : 0) | (c->sec_mark == 2 ? DM_CHEAT_SECTION_END : 0)
         | (c->pair >= 0 ? (c->pair_off ? DM_CHEAT_PAIR_OFF : DM_CHEAT_PAIR_ON) : 0) | (c->once ? DM_CHEAT_ONCE : 0)
         | (c->ask ? DM_CHEAT_ASK : 0) | (c->nd ? DM_CHEAT_HOST : 0) | (c->weak ? DM_CHEAT_WEAK : 0);
}

int dm_cheat_on_at(int i) { return i >= 0 && i < g_ncheat ? g_cheat[i].on != 0 : 0; }

// The menu's toggle: flip the cheat, save the states. A pair is one switch: turning its on half off runs the off half (the
// restore) for one pass, turning the on half on turns the off half off, and turning the off half on turns the on half off.
// Turning a cheat on ends safe mode (the player chose: the saved toggles come back too) and starts a never-decrease from
// the value there now
void dm_cheat_toggle(int i) {
    if (i < 0 || i >= g_ncheat) return;
    pthread_mutex_lock(&g_lock);
    cheat_t *c = &g_cheat[i];
    if (!c->master && !c->broken && !c->dead && !c->label) {
        int now = !c->on;
        if (now && g_safe) { g_safe = 0; states_load(); }   // the player turns a cheat on in safe mode: the saved toggles come back first
        c->on = (uint8_t)now;
        c->restore_once = 0;   // the player's own choice: a pending one-pass restore no longer applies
        if (now) c->nd_have = 0;
        if (c->pair >= 0) {
            cheat_t *p = &g_cheat[c->pair];
            if (!c->pair_off) { if (!p->broken && !p->dead) { p->on = (uint8_t)!now; p->restore_once = (uint8_t)!now; } }
            else if (now) p->on = 0;
        }
        states_save();
    }
    pthread_mutex_unlock(&g_lock);
}

// "Reload cheats": re-read the file (the same path), so edits during play do not need a re-launch
void dm_cheats_reload(void) {
    pthread_mutex_lock(&g_lock);
    load_all();
    pthread_mutex_unlock(&g_lock);
}

// The dry run: what cheat i would write right now, one line per write ("main+0x… (2 bytes): 37 -> 999"), nothing written
// and nothing turned off (static registers and never-decrease state are left as they were). Returns the number of writes
int dm_cheat_preview(int i, char *out, size_t cap) {
    if (!out || !cap) return 0;
    out[0] = 0;
    if (i < 0 || i >= g_ncheat) return 0;
    pthread_mutex_lock(&g_lock);
    cheat_t *c = &g_cheat[i];
    g_dry_out = out; g_dry_cap = cap; g_dry_len = 0; g_dry_writes = 0;
    if (c->label) dry_line("a label, not a cheat");
    else if (c->broken || c->dead) dry_line("does not run:%s", c->why);
    else if (c->nd) {
        unsigned w = type_width(c->type); uint64_t cur = 0; char where[48], now[48], mx[48];
        uint64_t base = c->nd_region == 0 ? (g_main_mod ? (uint64_t)(uintptr_t)g_main_mod->base : 0) : region_base(1);
        addr_name(base + c->nd_off, where, sizeof where);
        if (!base || peek(base + c->nd_off, w, &cur)) dry_line("%s: not mapped right now", where);
        else {
            value_text(c, w, cur, now, sizeof now);
            if (c->on && c->nd_have) { value_text(c, w, c->nd_max, mx, sizeof mx); dry_line("%s: %s now, kept at least %s (the highest seen)", where, now, mx); }
            else dry_line("%s: %s now; turned on, it never goes below the highest value it reaches", where, now);
        }
    } else {
        static uint64_t keep[256];
        memcpy(keep, g_static, sizeof keep);
        memset(g_reg, 0, sizeof g_reg); memset(g_looptop, 0, sizeof g_looptop);
        g_dry = 1; vm_run(c); g_dry = 0;
        memcpy(g_static, keep, sizeof keep);
        if (!g_dry_writes && !g_dry_len) dry_line("writes nothing right now (a condition is not met, or a patch's code is not the original any more)");
    }
    int n = g_dry_writes;
    g_dry_out = NULL;
    pthread_mutex_unlock(&g_lock);
    return n;
}

// The value of an "ask" cheat as text (1), or 0 when it takes none
int dm_cheat_value_get(int i, char *out, size_t cap) {
    if (!out || !cap) return 0;
    out[0] = 0;
    if (i < 0 || i >= g_ncheat || !g_cheat[i].ask) return 0;
    pthread_mutex_lock(&g_lock);
    value_get(&g_cheat[i], out, cap);
    pthread_mutex_unlock(&g_lock);
    return 1;
}

// Set an "ask" cheat's value (text in its type, within its bounds) and remember it in <build>.values: 0 done, -1 refused
int dm_cheat_value_set(int i, const char *text) {
    if (i < 0 || i >= g_ncheat) return -1;
    pthread_mutex_lock(&g_lock);
    int r = value_set_locked(&g_cheat[i], text);
    if (!r) values_save();
    pthread_mutex_unlock(&g_lock);
    return r;
}

// The bounds of an "ask" cheat's value as "min..max" (either side empty when open), "" when it takes none
const char *dm_cheat_value_bounds(int i) {
    static char b[64];
    b[0] = 0;
    if (i < 0 || i >= g_ncheat || !g_cheat[i].ask) return b;
    const cheat_t *c = &g_cheat[i];
    char lo[24] = "", hi[24] = "";
    if (c->has_min) snprintf(lo, sizeof lo, "%g", c->vmin);
    if (c->has_max) snprintf(hi, sizeof hi, "%g", c->vmax);
    snprintf(b, sizeof b, "%s..%s", lo, hi);
    return b;
}

// The master switch: off stops every cheat (masters too) without touching the toggles; kept in the folder's .cheats-off-<title>
int dm_cheats_master(void) { return atomic_load(&g_master); }

void dm_cheats_master_set(int on) {
    pthread_mutex_lock(&g_lock);
    atomic_store(&g_master, !!on);
    if (g_dir[0]) {
        char p[1100]; flag_file(p, sizeof p, "off");
        if (on) unlink(p);
        else { FILE *f = fopen(p, "w"); if (f) fclose(f); }
    }
    report_build();
    running_update();
    pthread_mutex_unlock(&g_lock);
}

// Safe mode (the last run ended without a clean exit while cheats were on): 1 while every cheat waits for the player
int dm_cheats_safe(void) { return g_safe; }

// Leave safe mode: the masters run again and the saved toggles come back
void dm_cheats_safe_restore(void) {
    pthread_mutex_lock(&g_lock);
    if (g_safe) {
        g_safe = 0;
        states_load();
        report_build();
        running_update();
    }
    pthread_mutex_unlock(&g_lock);
}

const char *dm_cheats_report(void) { return g_report; }

int dm_cheats_nskipped(void) { return g_nskip; }

const char *dm_cheats_skipped_name(int i) { return i >= 0 && i < g_nskip ? g_skip_name[i] : ""; }

const char *dm_cheats_skipped_why(int i) { return i >= 0 && i < g_nskip ? g_skip_why[i] : ""; }

int dm_cheats_nsources(void) { return g_nsrc; }

const char *dm_cheats_source(int i) { return i >= 0 && i < g_nsrc ? g_src[i] : ""; }
