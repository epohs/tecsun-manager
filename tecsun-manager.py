#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.14"
# dependencies = [
#     "mutagen==1.48.1",         # the web playlist's play times; imported when it's made
#     "pillow==12.3.0",          # the playlist EPUB's cover (reportlab needs it too); imported when it's made
#     "prompt-toolkit==3.0.53",  # imported directly, and its internals are relied on: see setup_question
#     "questionary==2.1.1",
#     "reportlab==5.0.1",        # the printed playlist; imported when it's made
#     "rich==15.0.0",
# ]
# ///

# tecsun-manager: the Tecsun PL-990x's SD card and its backups, in one place.
# Copyright (C) 2026 epohs
#
# This program is free software: you can redistribute it and/or modify it under the terms of the GNU General
# Public License as published by the Free Software Foundation, either version 3 of the License, or (at your
# option) any later version.
#
# This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the
# implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License
# for more details.
#
# You should have received a copy of the GNU General Public License along with this program. If not, see
# <https://www.gnu.org/licenses/>.
#
# SPDX-License-Identifier: GPL-3.0-or-later

"""tecsun-manager: the Tecsun PL-990x's SD card and its backups, in one place.

  Add albums         copy new albums onto the card, each at its number
  Arrange albums     move, rename or delete albums; the rest renumber
  Clean the card     remove macOS hidden files, re-sort, eject
  Back up            the card or a folder, into an archive with checksums and repair data
  Restore            unpack a backup and check every file
  Check              verify a backup, find damaged tracks, read and fix the card's play order
  Stats              albums, tracks and formats at a glance
  Generate playlist  the card's albums as a list: an EPUB for the X4, a PDF to print, a web page

Run it with no arguments for the menu; `tecsun-manager --help` is the short guide.
macOS and Linux. Python 3.14+ (for the built-in zstd), run through uv.
"""

import argparse
import bisect
import difflib
import errno
import fcntl
import functools
import glob
import hashlib
import html
import io
import itertools
import json
import logging
import math
import os
import platform
import plistlib
import re
import shlex
import shutil
import signal
import struct
import subprocess
import sys
import tarfile
import termios
import textwrap
import threading
import time
import traceback
import unicodedata
import uuid
import xml.parsers.expat
import zipfile
from collections import Counter
from compression import bz2, gzip, lzma, zstd
from concurrent.futures import ThreadPoolExecutor, as_completed
from contextlib import ExitStack, contextmanager, nullcontext, suppress
from dataclasses import dataclass, field
from datetime import UTC, datetime
from pathlib import Path

import questionary
from prompt_toolkit.application import get_app
from prompt_toolkit.completion import Completer, Completion, PathCompleter
from prompt_toolkit.filters import Condition
from prompt_toolkit.key_binding import KeyBindings, merge_key_bindings
from prompt_toolkit.layout import ConditionalContainer, FormattedTextControl, Window
from prompt_toolkit.shortcuts import CompleteStyle
from questionary import Choice, Separator
from questionary.prompts.common import InquirerControl
from rich.console import Console
from rich.markup import escape as esc
from rich.progress import (
    BarColumn,
    Progress,
    SpinnerColumn,
    TaskProgressColumn,
    TextColumn,
    TimeElapsedColumn,
    TimeRemainingColumn,
)
from rich.text import Text
from rich.theme import Theme

VERSION = "1.0.0"
PURPOSE = "the PL-990x radio's SD card"   # in the header, so what it's for shows before anything else
PROG = "tecsun-manager" if shutil.which("tecsun-manager") else "./tecsun-manager.py"  # in suggested commands



# ── Settings: edit to taste ───────────────────────────────────────────────────

AUDIO_EXTS = {"flac", "mp3", "wav", "m4a", "aac", "ogg", "wma", "ape", "alac", "aiff", "aif"}

# fatsort's order: natural ("2 - x" before "10 - x" without zero-padding), case ignored.
# fatsort_key predicts exactly this order for the checks, so change both or neither.
FATSORT_FLAGS = ["-n", "-c"]

PARITY_PERCENT = 10           # par2 repair data, as a % of the archive; 0 turns it off
ZSTD_LEVEL = 3                # audio barely compresses at any level; 3 runs at disk speed
RADIO_MAX_CARD = 128 * 10**9  # the PL-990x reads microSD cards up to 128 GB

# Backups go here unless another folder is typed at "Save the backup where?", which is then remembered in the
# state file until another is typed.
DEFAULT_BACKUPS = Path(__file__).resolve().parent / "tecsun-backups"  # sorts beside the script

# Generate playlist writes tecsun-playlist.epub, .pdf and .html here, beside the script, unless another name is
# typed.
PLAYLIST_FOLDER = Path(__file__).resolve().parent
PRINT_FONT_SIZE = 10.5        # the printed playlist's type, in points

STATE_FILE = Path(os.environ.get("XDG_CONFIG_HOME") or Path.home() / ".config") / "tecsun-manager" / "state.json"
LOGS_SPACE = 5 * 10**6        # every run's log together, in logs/ beside the state file; the oldest go first



# ── Constants ─────────────────────────────────────────────────────────────────

IS_MAC = sys.platform == "darwin"
HOME = Path.home()

RUN_LOG_DETAIL = LOGS_SPACE // 5  # past this, a run's log keeps what was shown, asked and changed, not each file

# OS clutter that never belongs on the card or in a backup.
JUNK_DIRS = {".Spotlight-V100", ".fseventsd", ".Trashes", ".TemporaryItems", ".DocumentRevisions-V100", ".AppleDouble"}
JUNK_FILES = {".DS_Store", ".apdisk"}
WINDOWS_DIRS = {"system volume information", "$recycle.bin"}  # Windows makes these on any drive it sees; never albums

# macOS guards these two. A stale .Trashes can hold a whole second library that the radio trips over.
PROTECTED_JUNK = (".Spotlight-V100", ".Trashes")

FAT_FAMILY = {"fat", "fat12", "fat16", "fat32", "exfat"}  # "fat": FAT of unknown size
REFORMAT_AS = {"exfat": "ExFAT", "fat32": "MS-DOS FAT32", "fat16": "MS-DOS FAT16", "fat12": "MS-DOS FAT12"}
FAT_BAD_NAME = re.compile(r'[\x00-\x1f"*:<>?\\|]|[ .]$')
FAT_MAX_NAME = 255     # UTF-16 units, as FAT stores long names
NAME_ROOM = len(" (renaming 99)")  # the most a temporary name adds (.Track.flac.part, Album (renaming 2)), so it fits too

ARCHIVE_SUFFIXES = (".tar.zst", ".tar.xz", ".tar.bz2", ".tar.gz")
FAT_MAX_FILE = 2**32 - 1      # FAT32 can't hold a single file bigger than this
FOUR_GB_FILESYSTEMS = {"msdos", "vfat", "fat", "fat12", "fat16", "fat32"}  # filesystem_of's names for FAT

# Reader and card names that mean "SD card" (but not "SSD").
SD_HINT = re.compile(r"(?<![A-Za-z])SD(HC|XC)?\b|microSD|(?i:card|reader|MMC)")

# Never a card, a backup destination or a restore target in their own right.
NEVER_TOUCH = {
    Path(p).resolve()
    for p in ("/", "/Users", "/home", "/Volumes", "/media", "/mnt", "/run/media", "/System", "/Library",
              "/Applications", "/private", "/usr", "/var", "/etc", "/opt", "/bin", "/sbin", "/tmp", HOME)
}

BACK = object()   # a task returns this when the user backs out to the menu
QUIT = object()   # the menu's Quit, which Esc also picks


@dataclass
class Run:
    """What this run knows besides its options, in one place: main() starts it fresh."""
    task: str = ""                     # the task under way; the line above each question names it
    doing: tuple | None = None         # (verb, what, red): what's being done to what, once the task has picked it
    active: tuple | None = None        # (card, album count) once confirmed: at the right of that line until ejected
    confirmed: tuple | None = None     # (card ID, every drive's ID then) once "Is this the right card?" is Yes
    card_in_use: Card | None = None    # the card being written, so an interrupt can say it wasn't ejected
    used: dict = field(default_factory=dict)      # card ID: Card, each card picked and not yet ejected
    declined: set = field(default_factory=set)    # IDs of cards whose clean-and-eject was turned down
    in_menu: bool = False              # tasks return to the menu, so a card can stay mounted for the next
    argv: list = field(default_factory=list)  # how the run was started, for a log turned on partway
    work: tuple | None = None          # (copied, of) while Add copies tracks, so a stop can say how far it got
    said: set = field(default_factory=set)        # hints already given this run, which needn't come again
    log: Path | None = None            # this run's log, once it's started
    pages: int = 0                     # pages begun this run: each after the first is dated
    clean_pages: bool = False          # Keep scrollback off: each pick from the menu clears the window first
    failed: bool = False              # something went wrong (a red line): the run exits 1
    task_failed: bool = False          # ... in the task under way, so its last line isn't green

    def reset(self) -> None:
        self.__init__()


RUN = Run()
LOG = logging.getLogger("tecsun-manager")
LOG.propagate = False
LOG.addHandler(logging.NullHandler())     # until start_log, and with logging off: nothing written, nothing printed
logging.raiseExceptions = False            # a log that can't be written never shows up, let alone stops the run



# ── Terminal UI ───────────────────────────────────────────────────────────────
# A light take on clack: a left rail, ◆ for a question, ◇ once it's answered.

THEME = Theme({
    "rail": "bright_black",
    "hint": "bright_black",
    "accent": "cyan",
    "ok": "green",
    "warn": "yellow",
    "bad": "red",
    "strong": "bold",
    "version": "yellow",
    "heading": "bold blue",
    "term": "green",
})
console = Console(highlight=False, theme=THEME)
errors = Console(stderr=True, highlight=False, theme=THEME)  # warnings, failures and stops: stderr, so they show past a > redirect

QSTYLE = questionary.Style([
    ("qmark", "fg:ansicyan bold"),
    ("question", "bold"),
    ("answer", "fg:ansicyan"),
    ("pointer", "fg:ansicyan bold"),
    ("highlighted", "fg:ansicyan"),
    ("selected", "fg:ansicyan"),
    ("instruction", "fg:ansibrightblack"),
    ("hint", "fg:ansibrightblack"),
    ("disabled", "fg:ansibrightblack"),
    ("text", ""),
    ("rail", "fg:ansibrightblack"),
    ("task", "fg:ansicyan bold"),
    ("danger", "fg:ansired bold"),
    ("subject", "bold"),
    ("accent", "fg:ansicyan"),
    ("pick", "fg:ansigreen"),            # an action that uses the place you're in
    ("nav", "fg:ansiblue"),              # an action that moves around
    ("separator", "fg:ansibrightblack"),
    ("warn", "fg:ansiyellow"),           # an action that needs doing: a card left mounted
])


def _line(mark: str, style: str, body: str | Text = "", to: Console | None = None) -> None:
    """One mark and its text, on `to` (stdout's console unless said). Long text wraps with the rail carried
    down, so the left edge stays unbroken."""
    to = to or console
    if not body:
        to.print(Text(mark, style=style))
        return
    text = body if isinstance(body, Text) else Text.from_markup(body)
    LOG.info("%s  %s", mark, text.plain)
    carry = Text(" " if mark == "└" else "│", style="rail")
    tint = "" if style == "rail" else style  # done, warnings and failures take their mark's color; the rest is plain
    for number, line in enumerate(text.wrap(to, max(20, to.width - 3))):
        lead = Text(mark, style=style) if number == 0 else carry.copy()
        # assemble, not lead + line: + would carry the mark's style under the whole line
        to.print(Text.assemble(lead, "  ", line, style=tint), no_wrap=True, crop=False)


def say(body: str | Text = "") -> None:
    """│  text. Markup is allowed, so pass user data through esc()."""
    _line("│", "rail", body)


def done(body: str | Text) -> None:
    _line("◇", "ok", body)


def warn(body: str | Text) -> None:
    _line("▲", "warn", body, errors)


def fail(body: str | Text) -> None:
    """Something went wrong, said in red: the task's last line won't be green, and the run exits 1."""
    RUN.failed = RUN.task_failed = True
    _line("■", "bad", body, errors)


def outro(body: str, good: bool = True, to: Console | None = None) -> None:
    """A task's last line. After a failure in that task it's never green."""
    _line("└", "rail", f"[{'ok' if good and not RUN.task_failed else 'warn'}]{body}[/]", to)


def page_break() -> None:
    """Above a page's first line, from the second page on: a line across the terminal with the time, so the
    newest page is easy to find when scrolling back, and matched to the log. With Keep scrollback off, pages
    start on a clean window instead, so there's nothing to mark."""
    if RUN.pages and not RUN.clean_pages:
        stamp = datetime.now().strftime("%H:%M")
        console.print(Text.assemble(("─" * max(0, console.width - len(stamp) - 4) + " ", "rail"), (stamp, "hint"),
                                    (" ──", "rail")), no_wrap=True, crop=True)
    RUN.pages += 1


def clear_screen() -> None:
    """Empty the window and its scrollback, as `clear` does, for Keep scrollback off. It stays the terminal's
    own screen, so a page taller than the window still scrolls back to its top, and whatever ends the run
    stays in view."""
    if console.is_terminal:
        console.file.write("\x1b[H\x1b[2J\x1b[3J")  # home, clear the window, clear the scrollback
        console.file.flush()


def header() -> None:
    """A page's first line: the name and what it's for."""
    page_break()
    console.print(Text.assemble(("┌", "rail"), "  ", ("Tecsun Manager", "bold"), ("  ·  ", "rail"), PURPOSE))


def intro(tools: Tools) -> None:
    """The header, and a tool that's missing, named once a run with what it costs."""
    header()
    missing = [] if tools.fatsort else [(["fatsort"], "the card can't be put in play order")]
    missing += [] if tools.par2 else [(["par2"], "backups get no repair data")]
    # Either finds damage, so only both missing is said: flac checks FLAC best, ffmpeg checks every format
    missing += [] if tools.flac or tools.ffmpeg else [(["flac", "ffmpeg"], "damaged tracks can't be found")]
    for names, cost in missing:
        if once(f"missing {names[0]}"):
            who = " and ".join(names) + (" aren't" if len(names) > 1 else " isn't")
            warn(f"{who} installed, so {cost}: {install_hint(*names)}")
    say()


def once(hint: str) -> bool:
    """True the first time a run asks about `hint`: for advice that needn't come again."""
    if hint in RUN.said:
        return False
    RUN.said.add(hint)
    return True


def boxed(lines: list[Text], title: str = "") -> None:
    """A small box on the rail, for summaries, with a title in its top edge if given."""
    limit = max(20, console.width - 10)
    for line in lines:
        line.truncate(limit, overflow="ellipsis")
    width = max(max(line.cell_len for line in lines) + 2, len(title) + 4)
    top = f" {title} " + "─" * (width - len(title) - 2) if title else "─" * width
    say(Text("┌" + top + "┐", style="hint"))
    for line in lines:
        say(Text.assemble(("│ ", "hint"), line, " " * (width - 1 - line.cell_len), ("│", "hint")))
    say(Text("└" + "─" * width + "┘", style="hint"))


def listing(items: list[str], limit: int = 8, mark: str = "[bad]✗[/]") -> None:
    for item in items[:limit]:
        say(f"  {mark} {esc(item)}")
    if len(items) > limit:
        say(f"  [hint]… {len(items) - limit} more[/]")


@dataclass
class Receipt:
    """What a task changed on the card, shown in a box at its end, so it's plain afterwards what's different:
    a row per album (a mark, its name, a note), counts for what needs no row of its own, and the play order once
    it's checked, which isn't a change of its own."""
    rows: list = field(default_factory=list)
    counts: list = field(default_factory=list)
    order: str = ""

    def add(self, mark: str, name: str, note: str = "") -> None:
        self.rows.append((mark, name, note))


RECEIPT_MARKS = {"+": "ok", "−": "bad", "~": "accent", "↑": "accent", "↓": "accent", "↕": "accent", "✎": "accent",
                 "↻": "accent"}


def show_receipt(card: Card, receipt: Receipt, limit: int = 8) -> None:
    """The receipt box, titled with the card, when anything changed: up to `limit` rows, then the counts and the
    play order. A renumber alone has no rows, only a count, and still gets its box."""
    if not (receipt.rows or receipt.counts):
        return
    rows = receipt.rows[:limit]
    width = min(44, max((len(nfc(name)) for _, name, _ in rows), default=0))
    lines = [Text.assemble((f"{mark} ", RECEIPT_MARKS.get(mark, "")), short(nfc(name), width).ljust(width),
                           ("  " + nfc(note) if note else "", "hint")) for mark, name, note in rows]
    more = [f"… {len(receipt.rows) - limit} more"] if len(receipt.rows) > limit else []
    footer = more + receipt.counts + ([receipt.order] if receipt.order else [])
    lines.append(Text(" · ".join(footer), style="hint"))
    boxed(lines, title=f"{card.name} now")


def progress_bar() -> Progress:
    return Progress(
        TextColumn("[rail]│[/] "),
        SpinnerColumn("dots", style="accent"),
        BarColumn(bar_width=24, complete_style="ok", finished_style="ok", pulse_style="hint"),
        TaskProgressColumn(),
        TextColumn("{task.fields[detail]}", style="strong"),
        TextColumn("[hint]·[/]"),
        TimeRemainingColumn(compact=True),
        TextColumn("{task.fields[note]}", style="hint", markup=False),
        console=console,
        transient=True,
    )


@contextmanager
def busy(label: str):
    """A spinner on the rail for steps without a percentage."""
    # The label goes in as a field, not the template: TextColumn formats its template, so a card named "A{B}"
    # would raise there.
    with Progress(TextColumn("[rail]│[/] "), SpinnerColumn("dots", style="accent"), TextColumn("{task.fields[label]}"),
                  TimeElapsedColumn(), console=console, transient=True) as bar:
        bar.add_task("", total=None, label=label)
        yield



# ── Prompts ───────────────────────────────────────────────────────────────────
# Each prompt erases itself when answered and leaves one "◇ question  answer" line.

def _answered(message: str, answer: str) -> None:
    LOG.info("◇  %s  → %s", message, answer)
    console.print(Text.assemble(("◇", "ok"), "  ", (message, "hint"), "  ", (answer, "accent")))
    say()


def option(label: str, value, hint: str = "", *, width: int = 0, plain: bool = False,
           disabled: str | None = None, description: str | None = None) -> Choice:
    """A menu choice. `plain` gives a plain-text label, which type-to-filter lists need."""
    if plain or disabled:
        return Choice(title=f"{label.ljust(width)}  {hint}".rstrip(), value=value, disabled=disabled)
    title = [("class:text", label.ljust(width))]
    if hint:
        title.append(("class:hint", "  " + hint))
    return Choice(title=title, value=value, description=description)


class StyledTitle(list):
    """A choice's styled title that type-to-filter can still search (it reads title.lower()). `label` is
    what's echoed once it's picked."""

    def __init__(self, tokens: list[tuple[str, str]], label: str):
        super().__init__(tokens)
        self.label = label

    def __str__(self) -> str:
        return "".join(text for _, text in self)

    def lower(self) -> str:
        return str(self).lower()


def action_choice(label: str, value, icon: str, *, style: str = "nav", hint: str = "") -> Choice:
    """A choice that does something, rather than naming something listed: an icon and a color of its own,
    green (`pick`) for using the place you're in, blue (`nav`, purple in many themes) for moving around."""
    label = nfc(label)
    tokens = [(f"class:{style}", f"{icon} {label}")] + ([("class:hint", "  " + hint)] if hint else [])
    return Choice(title=StyledTitle(tokens, label), value=value)


def back(label: str = "Back") -> Choice:
    return action_choice(label, BACK, "←")


def divider() -> Separator:
    """The line between what's listed and the actions under it."""
    return Separator("─" * 13)


def group(heading: str = "") -> Separator:
    """A heading in a list, for a group of choices under it: the menu's On the card, Backups, Info. Without one,
    a line as long, before the menu's Help, Settings and Quit."""
    return Separator(f"{heading} " + "─" * max(3, 22 - len(heading)) if heading else "─" * 23)


def task_line() -> list[tuple[str, str]]:
    """What's being done to what ("Moving  03 - Morning Edition"), or before that the task."""
    if RUN.doing:
        verb, what, red = RUN.doing
        return [("class:rail", "│  "), ("class:danger" if red else "class:task", verb), ("", "  "), ("class:subject", what)]
    if RUN.task:
        return [("class:rail", "│  "), ("class:task", RUN.task)]
    return []


def card_status() -> list[tuple[str, str]]:
    """The confirmed card: name, albums, free space. Empty once it's gone."""
    if RUN.active is None:
        return []
    card, albums = RUN.active
    try:
        free = shutil.disk_usage(card.mount).free
    except OSError:
        return []
    return [("class:accent", card.name), ("class:hint", f" · {plural(albums, 'album')} · {human(free)} free")]


def side_by_side(left: list, right: list, width: int) -> list:
    """`left` and `right` on one line, `right` ending where the header's does; `right` on a line of its
    own above when they don't both fit."""
    size = lambda tokens: sum(len(text) for _, text in tokens)
    edge = min(width, 80)
    if not right:
        return left
    if size(left) + 2 + size(right) <= edge:
        return [*(left or [("class:rail", "│")]), ("", " " * (edge - (size(left) or 1) - size(right))), *right]
    return [("class:rail", "│"), ("", " " * max(1, edge - 1 - size(right))), *right, ("", "\n"), *left]


@contextmanager
def doing(verb: str, what: str, *, red: bool = False):
    """While inside, the line above each question says what's being done to what."""
    before, RUN.doing = RUN.doing, (verb, what, red)
    try:
        yield
    finally:
        RUN.doing = before


# Inside a task, every question shows on the line above it what's being done to what, or the task's name
# until something's picked. Esc backs out of every
# question: a list picks its Back choice (Quit in the menu), a yes/no question answers No or goes back
# where the caller asks, a typed field goes back. Option-arrows and Option-delete send
# Esc plus a key, so a lone Esc waits a moment for a second key, and those still move and delete by word.
def setup_question(question, escape, enter=None):
    app = question.application
    left, right = task_line(), card_status()
    if left or right:
        app.layout.container.children.insert(0, Window(
            FormattedTextControl(lambda: side_by_side(left, right, get_app().output.get_size().columns)),
            dont_extend_height=True, wrap_lines=True))
    bindings = KeyBindings()
    bindings.add("escape")(escape)
    bindings.add("escape", "enter")(lambda event: None)  # Option+Return: Meta+Enter would accept ""
    if enter:
        bindings.add("enter", eager=True)(enter)
    app.key_bindings = merge_key_bindings([app.key_bindings, bindings])
    app.ttimeoutlen = app.timeoutlen = 0.05
    return question


def ask_select(message: str, choices: list[Choice], default=None, *, search: bool = False, echo: bool = True,
               on_escape=BACK, esc_hint: str = "Esc goes back", on_pick=None):
    """Pick one. Esc picks the choice whose value is `on_escape`, the Back choice unless said otherwise;
    with a filter typed, Esc clears the filter first. `on_pick` gets the answer before it's echoed."""
    leaves = any(c.value is on_escape for c in choices)
    hints = (["type to filter"] if search else []) + ([esc_hint] if leaves and esc_hint else [])
    for choice in choices:  # typed accents are composed; macOS lists names on the card decomposed
        if isinstance(choice.title, str):
            choice.title = nfc(choice.title)
    question = questionary.select(
        message, choices=choices, default=default, qmark="◆ ", pointer="●", style=QSTYLE,
        instruction=" · ".join(hints) or " ", use_search_filter=search, use_jk_keys=not search,
        erase_when_done=True,
    )
    control = next(c for c in question.application.layout.find_all_controls() if isinstance(c, InquirerControl))
    # questionary checks the row under the pointer in the whole list, though the pointer counts the rows shown:
    # with a filter typed, the arrows would skip a row past the line
    control.is_selection_valid = lambda: not control.get_pointed_at().disabled  # a Separator is always disabled
    if search:
        show_filter(question, control)

    def escape(event) -> None:
        if control.search_filter:  # the pointer stays on the same choice
            shown = control.filtered_choices
            current = shown[control.pointed_at] if control.pointed_at < len(shown) else None
            control.search_filter = None
            control.pointed_at = control.choices.index(current) if current in control.choices else 0
        elif leaves:
            event.app.exit(result=on_escape)

    def enter(event) -> None:
        if control.search_filter and not filter_matches(control):
            return  # questionary shows the whole list when nothing matches; Enter would pick its first item
        if isinstance(control.get_pointed_at(), Separator):
            return  # clearing a filter can leave the pointer on the line
        control.is_answered = True
        event.app.exit(result=control.get_pointed_at().value)

    value = setup_question(question, escape, enter).unsafe_ask()
    picked = next(c for c in choices if c.value is value)  # by identity: 0 == False would match the wrong one
    label = getattr(picked.title, "label", None) or (picked.title[0][1] if isinstance(picked.title, list)
                                                     else picked.title)
    if on_pick:
        on_pick(value)
    if echo:
        _answered(message, label.strip())
    else:
        LOG.info("◇  %s  → %s", message, label.strip())
    return value


def show_filter(question, control: InquirerControl) -> None:
    """Swap questionary's filter line, "/ f..." under the list, for a plain one right under the question."""
    children = question.application.layout.container.children
    children[:] = [c for c in children if getattr(getattr(c, "content", None), "content", None) is None
                   or getattr(c.content.content, "text", None) != control.get_search_string_tokens]
    at = next(i for i, c in enumerate(children) if getattr(getattr(c, "content", None), "content", None) is control)
    typed = lambda: control.search_filter or ""
    children.insert(at, ConditionalContainer(Window(FormattedTextControl(lambda: filter_line(typed(), filter_matches(control))),
                                                    height=1), filter=Condition(lambda: bool(typed()))))


def filter_matches(control: InquirerControl) -> bool:
    """Whether what's typed matches any choice; the line between contents and actions doesn't count."""
    typed = (control.search_filter or "").lower()
    return any(typed in str(c.title).lower() for c in control.choices if not isinstance(c, Separator))


def filter_line(typed: str, matches: bool) -> list[tuple[str, str]]:
    keys = ("class:hint", "  · Backspace edits · Esc clears")
    if matches:
        return [("", "   "), ("class:hint", "showing names with "), ("class:accent", f'"{typed}"'), keys]
    return [("", "   "), ("class:danger", f'nothing matches "{typed}"'), keys]


def ask_confirm(message: str, default: bool = True, *, on_escape=False):
    """Yes or No. Esc answers `on_escape`: No, unless the caller needs a way back (BACK)."""
    question = questionary.confirm(
        message, default=default, qmark="◆ ", style=QSTYLE, auto_enter=True, erase_when_done=True,
    )
    answer = setup_question(question, lambda event: event.app.exit(result=on_escape)).unsafe_ask()
    if answer is not BACK:
        _answered(message, "Yes" if answer else "No")
    else:
        LOG.info("◇  %s  → Esc, back", message)
    return answer


def ask_go(go: str, *, safe: bool = False):
    """"Go ahead?", the last question before a change: "go" or BACK. The first choice names the change. `safe`:
    Enter alone goes back, for a change that drops something."""
    return ask_select("Go ahead?", [option(go, "go"), back()], default=BACK if safe else "go")


def typed_field(message: str, hint: str = "", **kwargs):
    """A typed answer, or BACK. Esc closes the suggestions first. The hint sits right after the question."""
    question = questionary.text(message, qmark="◆ ", style=QSTYLE, erase_when_done=True,
                                instruction=" · ".join(filter(None, [hint, "Esc goes back"])), **kwargs)

    def escape(event) -> None:
        if event.current_buffer.complete_state:
            event.current_buffer.cancel_completion()
        else:
            event.app.exit(result=BACK)

    answer = setup_question(question, escape).unsafe_ask()
    if answer is BACK:
        LOG.info("◇  %s  → Esc, back", message)
    return answer


def ask_text(message: str, default: str = ""):
    """Typed text, or BACK."""
    answer = typed_field(message, default=default)
    if answer is not BACK:
        _answered(message, answer)
    return answer


class PlacesCompleter(Completer):
    """Path completion, plus labeled shortcuts: last used, plugged-in drives, Desktop."""

    def __init__(self, places: list[tuple[str, str]], default: str, files: bool):
        self.places = places
        self.default = default
        self.paths = PathCompleter(
            only_directories=not files,
            expanduser=True,
            file_filter=(lambda name: os.path.isdir(name) or name.endswith(ARCHIVE_SUFFIXES)) if files else None,
        )

    def get_completions(self, document, complete_event):
        typed = document.text_before_cursor
        show_all = not typed.strip() or typed == self.default
        for path, label in self.places:
            if path != typed and (show_all or path.casefold().startswith(typed.casefold())):
                yield Completion(path, start_position=-len(typed), display=path, display_meta=label)
        if typed.strip() and not show_all:
            yield from self.paths.get_completions(document, complete_event)


def clean_path(raw: str) -> Path:
    """Accept typed, pasted or dragged-in paths (Terminal escapes spaces when you drag a file in). os.path's
    expanduser, since Path's raises on a "~" that names no home folder, and the field checks every keystroke."""
    text = raw.strip()
    if len(text) >= 2 and text[0] == text[-1] and text[0] in "'\"":
        text = text[1:-1]
    path = Path(os.path.expanduser(text))
    if not path.exists() and "\\" in text:
        path = Path(os.path.expanduser(re.sub(r"\\(.)", r"\1", text)))
    return Path(os.path.abspath(path))


def stray_tilde(raw: str) -> bool:
    """A "~" that names no home folder: "~V" or "~?", a slip for "~/". It would be a folder named "~V" here."""
    text = raw.strip().strip("'\"")
    return text.startswith("~") and os.path.expanduser(text).startswith("~")


def ask_path(message: str, default: str, places: list[tuple[str, str]], *, must_exist: bool,
             archive: bool = False, check=None):
    """A path field with Tab completion, or BACK. `check(path)` can return a reason to refuse it."""

    def validate(raw: str):
        if not raw.strip():
            return "Type a path, or press Tab for suggestions."
        if stray_tilde(raw):
            return "Start with ~/ for your home folder."
        path = clean_path(raw)
        if archive:
            if path.is_file() and path.name.endswith(ARCHIVE_SUFFIXES):
                return True
            return "Pick a backup file: .tar.zst, .tar.xz, .tar.bz2 or .tar.gz"
        if path.is_file():
            return "That's a file. Pick a folder."
        if must_exist and not path.is_dir():
            return "Can't find that folder."
        if not path.exists() and (drive := unplugged(path)):
            return f"{drive} isn't plugged in."
        if not path.exists() and nearest_existing(path) is None:
            return "Can't create a folder there."
        if path.resolve() in NEVER_TOUCH:
            return "Pick a folder inside this one."
        reason = check(path) if check else None
        return reason or True

    raw = typed_field(message, f"Tab for suggestions, or drag {'one' if archive else 'a folder'} in", default=default,
                      validate=validate,
                      completer=PlacesCompleter(places, default, files=archive), complete_style=CompleteStyle.COLUMN)
    if raw is BACK:
        return BACK
    path = clean_path(raw)
    _answered(message, tilde(path))
    return path



# ── Small helpers ─────────────────────────────────────────────────────────────

def run(cmd: list[str], *, cwd: Path | None = None, interactive: bool = False,
        timeout: float | None = 300, binary: bool = False, detail: bool = False) -> subprocess.CompletedProcess:
    """A command's result. A wedged card reader can hang a command, so each has a time limit, except those
    that must never be cut off halfway (fatsort, a reformat: they pass None). A command that timed out or
    isn't installed reads as failed (124, 127). `binary` keeps its output as bytes. `detail`: one of many
    (a track's check), logged as a detail when it succeeds."""
    started = time.monotonic()
    empty = b"" if binary else ""
    try:
        if interactive:
            result = subprocess.run(cmd, cwd=cwd, check=False)
        else:
            result = subprocess.run(cmd, cwd=cwd, stdin=subprocess.DEVNULL, capture_output=True, text=not binary,
                                    errors=None if binary else "replace", check=False, timeout=timeout)
    except subprocess.TimeoutExpired:
        result = subprocess.CompletedProcess(cmd, 124, empty, f"{cmd[0]} timed out")
    except FileNotFoundError:
        result = subprocess.CompletedProcess(cmd, 127, empty, f"{cmd[0]} isn't installed")
    log_command(result, time.monotonic() - started, detail)
    return result


def log_command(result: subprocess.CompletedProcess, seconds: float, detail: bool = False) -> None:
    """A command in the log: what ran, how it ended, how long it took, and when it failed, the end of what it
    said. sudo reads a password from the terminal itself, so none ever passes through here."""
    level = logging.DEBUG if detail and result.returncode == 0 else logging.INFO
    LOG.log(level, "$  %s  → %s in %.1fs", shlex.join(map(str, result.args)), result.returncode, seconds)
    said = result.stderr if isinstance(result.stderr, str) else (result.stderr or b"").decode(errors="replace")
    if result.returncode != 0 and said.strip():
        for line in said.strip().splitlines()[-4:]:
            LOG.info("   %s", line)


def natural_key(name: str) -> list:
    """Sort key where 2 comes before 10, case ignored. isdecimal, not isdigit: "²" is a digit int() can't read."""
    return [int(part) if part.isdecimal() else part.casefold() for part in re.split(r"(\d+)", nfc(name))]


def human(size: float) -> str:
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if abs(size) < 1000 or unit == "TB":
            return f"{size:.0f} {unit}" if unit in ("B", "KB") else f"{size:.1f} {unit}"
        size /= 1000


def plural(count: int, word: str, many: str | None = None) -> str:
    return f"{count:,} {word if count == 1 else (many or word + 's')}"


def tilde(path) -> str:
    text, home = str(path), str(HOME)
    return "~" + text[len(home):] if text == home or text.startswith(home + os.sep) else text


def short(name: str, width: int = 32) -> str:
    return name if len(name) <= width else name[: width - 1] + "…"


def nfc(text: str) -> str:
    return unicodedata.normalize("NFC", text)


def written(name: str) -> str:
    """A name to write or rename on the card. macOS's FAT driver lists names decomposed, but renames only
    by the composed spelling it stores, and can't rename a file it created under a decomposed name."""
    return nfc(name) if IS_MAC else name


def is_audio(path: Path) -> bool:
    return path.suffix[1:].lower() in AUDIO_EXTS


def nearest_existing(path: Path) -> Path | None:
    for candidate in (path, *path.parents):
        if candidate.is_dir():
            return candidate if os.access(candidate, os.W_OK) else None
    return None


def inside(child: Path, parent: Path) -> bool:
    child, parent = child.resolve(), parent.resolve()
    return child == parent or parent in child.parents


def unplugged(path: Path) -> str | None:
    """The drive a path under /Volumes is on, when it isn't plugged in, so nothing is made in its place."""
    parts = path.parts
    if IS_MAC and len(parts) > 2 and parts[1] == "Volumes" and not Path("/Volumes", parts[2]).is_dir():
        return parts[2]
    return None


def install_hint(*names: str) -> str:
    return ("brew install " if IS_MAC else "sudo apt install ") + " ".join(names)


def sidecar(archive: Path, suffix: str) -> Path:
    return archive.with_name(archive.name + suffix)


class SafetyError(Exception):
    """Raised when a guard fails; nothing else gets touched after it."""



# ── Remembered paths ──────────────────────────────────────────────────────────

STATE_TYPES = {"library": str, "card_uuid": str, "backup_dir": str, "last_archive": str, "restore_dir": str,
               "cards": dict, "debug_log": bool, "keep_scrollback": bool}


def load_state() -> dict:
    """What's remembered. Only values of the shape this script writes are kept, so a damaged or hand-edited
    file is at worst forgotten."""
    try:
        state = json.loads(STATE_FILE.read_text())
    except (OSError, ValueError):
        return {}
    if not isinstance(state, dict):
        return {}
    kept = {key: value for key, value in state.items() if isinstance(value, STATE_TYPES.get(key, object))}
    kept["cards"] = {uuid: card for uuid, card in kept.get("cards", {}).items() if isinstance(card, dict)}
    return kept


def remembered_time(stamp) -> datetime | None:
    """A time from the state file, or None when it isn't one (a hand-edited file)."""
    try:
        when = datetime.fromisoformat(stamp)
    except (TypeError, ValueError):
        return None
    return when if when.tzinfo else None  # every time written here has a zone; one without can't be compared


def local_date(stamp) -> str | None:
    """A remembered time as this computer's date, or None when it isn't one."""
    when = remembered_time(stamp)
    return when.astimezone().date().isoformat() if when else None


def backup_reminder(state: dict, card: Card) -> str | None:
    """A line saying a card has changed since its last backup, if this script changed it since. Changes made
    elsewhere (in Finder, or the device's own records) aren't known."""
    entry = state.get("cards", {}).get(card.uuid, {}) if card.uuid else {}
    changed, backed_up = remembered_time(entry.get("changed")), remembered_time(entry.get("backed_up"))
    if changed and backed_up and changed > backed_up:
        return (f"{esc(card.name)} has changed since it was last backed up, "
                f"{backed_up.astimezone().date().isoformat()}. Back up saves a new backup.")
    if changed and not backed_up:
        return f"{esc(card.name)} has changed, and has no backup yet. Back up saves one."
    return None


def backup_reminders(state: dict) -> list[str]:
    """The reminder for each card plugged in, for the menu."""
    return [note for card in list_cards() if (note := backup_reminder(state, card))]


def save_state(state: dict, **changes) -> bool:
    """Remember these. False when the file couldn't be written: remembering is a convenience, so a run never
    fails over it, but a setting the user picked should say it wasn't kept."""
    state.update(changes)
    try:
        STATE_FILE.parent.mkdir(parents=True, exist_ok=True)
        temp = STATE_FILE.with_suffix(".tmp")
        temp.write_text(json.dumps(state, indent=2))
        temp.replace(STATE_FILE)
    except OSError:
        return False
    return True


def remember_card(state: dict, card: Card) -> None:
    entry = state.setdefault("cards", {}).setdefault(card.uuid, {})
    entry.update(name=card.name, updated=datetime.now(UTC).isoformat(timespec="seconds"))
    save_state(state, card_uuid=card.uuid)



# ── Tools on this machine ─────────────────────────────────────────────────────

@dataclass
class Tools:
    fatsort: bool
    par2: bool
    flac: bool
    ffmpeg: bool
    dot_clean: bool
    udisksctl: bool
    full_disk_access: bool
    fatsort_version: tuple[int, ...] = ()

    @classmethod
    def detect(cls) -> Tools:
        have = lambda name: shutil.which(name) is not None
        fda = False
        if IS_MAC:
            # No API says "this terminal has Full Disk Access"; reading the TCC database only works with it.
            try:
                with open(HOME / "Library/Application Support/com.apple.TCC/TCC.db", "rb") as db:
                    fda = bool(db.read(1))
            except OSError:
                fda = False
        version = ()
        if have("fatsort"):
            found = re.search(r"(\d+(?:\.\d+)+)", run(["fatsort", "-v"]).stdout)
            version = tuple(int(n) for n in found.group(1).split(".")) if found else ()
        return cls(have("fatsort"), have("par2"), have("flac"), have("ffmpeg"),
                   have("dot_clean"), have("udisksctl"), fda, version)



# ── Finding cards ─────────────────────────────────────────────────────────────

@dataclass
class Card:
    name: str
    mount: Path
    device: str       # what fatsort works on, e.g. /dev/disk5s1
    whole: str        # the whole disk, for eject, e.g. /dev/disk5
    fs: str           # fat32, fat16, exfat, apfs, …
    fs_label: str     # FAT32, exFAT, APFS, …
    size: int
    free: int
    kind: str         # "SD card · built-in reader", "USB drive", "disk image", …
    uuid: str
    writable: bool

    def problem(self, *, changes: bool = True) -> str | None:
        """Why this card can't be picked, if it can't. A task that only reads (`changes` False) may use a locked
        card. An e-reader's card is never one to use: cleaning it would delete the e-reader's records."""
        if self.mount.resolve() in NEVER_TOUCH:
            return f"mounted at {self.mount}; give it its own folder"
        if self.fs not in FAT_FAMILY:
            return f"radio can't read {self.fs_label}"
        if changes and not self.writable:
            return "read-only: check the card's lock switch"
        if changes and not self.uuid:  # every write checks the card by its ID first, so none could go ahead
            return "no volume ID, so writes can't be checked to land on this card"
        if (self.mount / ".crosspoint").is_dir():
            return "an XTEINK e-reader's card: cleaning would delete its reading progress"
        return None


def list_cards() -> list[Card]:
    """Every mounted removable or external volume. The computer's own drives never appear."""
    return _mac_cards() if IS_MAC else _linux_cards()


def diskutil_info(target: str) -> dict:
    if not target:
        return {}
    try:
        result = subprocess.run(["diskutil", "info", "-plist", target], stdin=subprocess.DEVNULL,
                                capture_output=True, check=False, timeout=60)
    except subprocess.TimeoutExpired:
        return {}
    if result.returncode != 0:
        return {}
    try:
        return plistlib.loads(result.stdout)
    except (ValueError, xml.parsers.expat.ExpatError):
        return {}


def _removable(info: dict) -> bool:
    return bool(info.get("Removable") or info.get("RemovableMedia") or info.get("Ejectable"))


def _mac_cards() -> list[Card]:
    cards = []
    try:
        entries = sorted(Path("/Volumes").iterdir())
    except OSError:
        return cards
    for entry in entries:
        if entry.is_symlink() or not os.path.ismount(entry):
            continue
        volume = diskutil_info(str(entry))
        whole = volume.get("ParentWholeDisk", "")
        card = mac_card_from_info(volume, diskutil_info(whole) if whole else {})
        if card:
            cards.append(card)
    return cards


def mac_card_from_info(volume: dict, disk: dict, usage=shutil.disk_usage) -> Card | None:
    mount = volume.get("MountPoint") or ""
    if mount in ("", "/"):
        return None
    if volume.get("Internal") and not (_removable(volume) or _removable(disk)):
        return None  # the Mac's own drive
    try:
        space = usage(mount)
    except OSError:
        return None

    kind_of = (volume.get("FilesystemType") or "").lower()
    name = volume.get("FilesystemName") or volume.get("FilesystemUserVisibleName") or kind_of
    if kind_of == "exfat":
        fs, fs_label = "exfat", "exFAT"
    elif kind_of == "msdos":
        bits = found.group(1) if (found := re.search(r"FAT(12|16|32)", name)) else "32"
        fs, fs_label = f"fat{bits}", f"FAT{bits}"
    else:
        fs, fs_label = kind_of or "unknown", name or "an unknown format"

    bus = disk.get("BusProtocol") or volume.get("BusProtocol") or ""
    media = f"{disk.get('MediaName', '')} {disk.get('IORegistryEntryName', '')}"
    if bus == "Disk Image":
        kind = "disk image"
    elif bus == "Secure Digital":
        kind = "SD card · built-in reader"
    elif SD_HINT.search(media):
        kind = f"SD card · {bus or 'USB'} reader"
    elif bus == "USB" and fs in FAT_FAMILY and space.total <= RADIO_MAX_CARD * 1.1:
        kind = "card or USB stick"  # plenty of readers name only their chip, e.g. "NORELSYS 1081CS0"
    else:
        kind = f"{bus} drive" if bus else "drive"

    whole = volume.get("ParentWholeDisk")
    return Card(
        name=volume.get("VolumeName") or Path(mount).name,
        mount=Path(mount),
        device=volume.get("DeviceNode", ""),
        whole=f"/dev/{whole}" if whole else volume.get("DeviceNode", ""),
        fs=fs, fs_label=fs_label,
        size=space.total, free=space.free,
        kind=kind,
        uuid=volume.get("VolumeUUID") or volume.get("DiskUUID") or "",
        writable=bool(volume.get("WritableVolume", True)),
    )


def _truthy(value) -> bool:
    return value in (True, 1, "1", "true")


def _linux_cards() -> list[Card]:
    columns = "NAME,PATH,PKNAME,TYPE,RM,HOTPLUG,TRAN,VENDOR,MODEL,LABEL,FSTYPE,FSVER,MOUNTPOINT,UUID,RO"
    result = run(["lsblk", "--json", "--bytes", "--list", "-o", columns], detail=True)
    if result.returncode != 0:
        return []
    try:
        return linux_cards_from_lsblk(json.loads(result.stdout), mount_types=_mount_types(),
                                      probe_uuid=_probe_uuid, mmc_type=_mmc_type)
    except ValueError:
        return []


def _mount_types() -> dict[str, str]:
    """Mount point to filesystem type, from the kernel's own table (lsblk needs udev for this)."""
    types = {}
    try:
        for line in Path("/proc/self/mounts").read_text().splitlines():
            _, mount, fs_type = line.split()[:3]
            types[re.sub(r"\\([0-7]{3})", lambda m: chr(int(m.group(1), 8)), mount)] = fs_type
    except (OSError, ValueError):
        pass
    return types


def _probe_uuid(device: str) -> str:
    """Read the ID from the device itself (-p skips blkid's cache, which can be stale)."""
    if not shutil.which("blkid"):
        return ""
    return run(["blkid", "-p", "-s", "UUID", "-o", "value", device], detail=True).stdout.strip()


def _mmc_type(name: str) -> str:
    """'SD' for a card in a slot, 'MMC' for built-in eMMC storage."""
    try:
        return Path(f"/sys/block/{name}/device/type").read_text().strip()
    except OSError:
        return ""


def linux_cards_from_lsblk(data: dict, usage=shutil.disk_usage, mount_types: dict | None = None,
                           probe_uuid=lambda device: "", mmc_type=lambda name: "") -> list[Card]:
    rows = data.get("blockdevices", [])
    by_name = {row.get("name"): row for row in rows}
    cards = []
    for row in rows:
        mount = row.get("mountpoint")
        if not mount or mount in ("/", "[SWAP]") or mount.startswith(("/boot", "/snap", "/efi")):
            continue
        parent = by_name.get(row.get("pkname")) or row
        loop = "loop" in (row.get("type"), parent.get("type"))

        kind_of = (row.get("fstype") or (mount_types or {}).get(mount) or "").lower()
        if kind_of == "exfat":
            fs, fs_label = "exfat", "exFAT"
        elif kind_of in ("vfat", "msdos", "fat"):
            bits = re.search(r"(12|16|32)", row.get("fsver") or "")
            fs, fs_label = (f"fat{bits.group(1)}", f"FAT{bits.group(1)}") if bits else ("fat", "FAT")
        else:
            fs, fs_label = kind_of or "unknown", kind_of or "an unknown format"

        # mmcblk is also built-in eMMC storage; the kernel says "SD" only for a card in a slot.
        parent_name = str(parent.get("name", ""))
        sd_slot = parent_name.startswith("mmcblk") and mmc_type(parent_name) == "SD"
        removable = loop or sd_slot or any(
            _truthy(source.get(key)) for source in (row, parent) for key in ("rm", "hotplug"))
        if not removable or (loop and fs not in FAT_FAMILY):
            continue  # internal drives, and loop mounts that are really snaps
        try:
            space = usage(mount)
        except OSError:
            continue

        transport = parent.get("tran") or ""
        label = f"{parent.get('vendor') or ''} {parent.get('model') or ''}"
        if loop:
            kind = "disk image"
        elif sd_slot:
            kind = "SD card · built-in reader"
        elif SD_HINT.search(label):
            kind = "SD card · USB reader"
        elif transport == "usb" and fs in FAT_FAMILY and space.total <= RADIO_MAX_CARD * 1.1:
            kind = "card or USB stick"
        else:
            kind = f"{transport.upper()} drive" if transport else "drive"

        device = row.get("path") or f"/dev/{row.get('name')}"
        cards.append(Card(
            name=row.get("label") or Path(mount).name,
            mount=Path(mount),
            device=device,
            whole=parent.get("path") or f"/dev/{parent.get('name')}",
            fs=fs, fs_label=fs_label,
            size=space.total, free=space.free,
            kind=kind,
            uuid=row.get("uuid") or probe_uuid(device),
            writable=not _truthy(row.get("ro")),
        ))
    return cards


def find_card(device: str, uuid: str | None = None) -> Card | None:
    """The card mounted from `device` now, and with the ID `uuid` when given (a reformat changes it)."""
    return next((c for c in list_cards() if c.device == device and uuid in (None, c.uuid)), None)


def device_still_matches(card: Card) -> bool:
    """Is the device still the card the user picked? Checked by its ID right before anything writes."""
    if not card.uuid:
        return False
    if IS_MAC:
        info = diskutil_info(card.device)
        removable = _removable(info) or not info.get("Internal")
        return bool(info) and removable and (info.get("VolumeUUID") or info.get("DiskUUID")) == card.uuid
    found = run(["lsblk", "-no", "UUID", card.device], detail=True).stdout.strip() or _probe_uuid(card.device)
    return found == card.uuid


def card_still_here(card: Card) -> bool:
    """Is the card's folder still mounted from the same device, with the same ID?"""
    root = card.mount
    if not os.path.ismount(root) or root.resolve() in NEVER_TOUCH:
        return False
    if IS_MAC:
        return diskutil_info(str(root)).get("DeviceNode") == card.device and device_still_matches(card)
    try:
        mounted_from_device = os.stat(root).st_dev == os.stat(card.device).st_rdev
    except OSError:
        return False
    return mounted_from_device and device_still_matches(card)



# ── What's on a card ──────────────────────────────────────────────────────────

@dataclass
class CardContents:
    albums: list[str] = field(default_factory=list)
    tracks: int = 0
    used: int = 0
    hidden: list[str] = field(default_factory=list)
    other_files: list[str] = field(default_factory=list)

    @property
    def empty(self) -> bool:
        return not self.albums and not self.tracks and not self.other_files


def scan_card(root: Path) -> CardContents:
    contents = CardContents()
    # An unreadable card stops the run with the reason, rather than passing for an empty one
    entries = sorted(os.scandir(root), key=lambda e: natural_key(e.name))
    for entry in entries:
        if entry.name.startswith("."):
            contents.hidden.append(entry.name)
        elif entry.name.casefold() in WINDOWS_DIRS:
            continue
        elif entry.is_dir(follow_symlinks=False):
            contents.albums.append(entry.name)
            for dirpath, dirnames, filenames in os.walk(entry.path):
                dirnames[:] = [d for d in dirnames if not d.startswith(".")]
                for name in filenames:
                    if name.startswith("."):
                        continue
                    path = Path(dirpath, name)
                    contents.used += path.stat().st_size
                    if is_audio(path):
                        contents.tracks += 1
                    else:
                        contents.other_files.append(str(path.relative_to(root)))
        elif entry.is_file():
            contents.used += entry.stat().st_size
            if is_audio(Path(entry.name)):
                contents.tracks += 1
            else:
                contents.other_files.append(entry.name)
    return contents


def show_card(card: Card, contents: CardContents, state: dict) -> None:
    lines = [Text(f"{human(card.size)} {card.kind} · {card.fs_label} · {human(card.free)} free")]
    if contents.empty:
        lines.append(Text("Empty"))
    else:
        lines.append(Text(f"{plural(len(contents.albums), 'album')} · {plural(contents.tracks, 'track')}"))
        if contents.albums:
            first = ", ".join(contents.albums[:3])
            more = f" … +{len(contents.albums) - 3} more" if len(contents.albums) > 3 else ""
            lines.append(Text(first + more))
    if contents.hidden:
        lines.append(Text(f"Hidden: {', '.join(contents.hidden[:3])}" + (" …" if len(contents.hidden) > 3 else ""),
                          style="hint"))
    if updated := local_date(state.get("cards", {}).get(card.uuid, {}).get("changed")):
        lines.append(Text(f"Last changed from this computer: {updated}", style="hint"))
    boxed(lines)

    if any(name.upper() == "DCIM" for name in contents.albums):
        warn("Has a DCIM folder. This may be a camera card.")
    if contents.other_files:
        warn(f"{plural(len(contents.other_files), 'file')} that aren't audio, e.g. {esc(contents.other_files[0])}")
    if card.size > RADIO_MAX_CARD:
        warn("Bigger than 128 GB. The PL-990x may not read it.")


def rank_cards(cards: list[Card], last_uuid: str | None, *, changes: bool = True) -> list[Card]:
    """Usable first, then the card used last time, then SD cards, with disk images last."""
    return sorted(cards, key=lambda c: (c.problem(changes=changes) is not None, c.uuid != last_uuid,
                                        not c.kind.startswith(("SD card", "card")), c.kind == "disk image",
                                        c.name.casefold()))


def choose_card(state: dict, *, changes: bool = True) -> tuple[Card, CardContents] | None:
    """Pick a card from the list, or the only one plugged in, see what's on it, confirm it's the right one. Once
    confirmed, later tasks in the same run use it without asking, as long as the same drives are plugged in. A
    task that only reads (`changes` False) may use a locked card."""
    while True:
        cards = list_cards()
        if card := still_confirmed(cards, changes=changes):
            say(f"[hint]Using {esc(card.name)}, confirmed earlier.[/]")
            RUN.used[card_key(card)] = card
            return card, scan_card(card.mount)
        if not cards:
            warn("No SD card found. Insert the card, then pick Rescan.")
            if ask_select("No card", [action_choice("Rescan", "rescan", "↻"), back()]) is BACK:
                return None
            continue

        last = state.get("card_uuid")
        cards = rank_cards(cards, last, changes=changes)
        if len(cards) == 1 and cards[0].problem(changes=changes) is None:
            picked = cards[0]
        else:
            width = max(len(c.name) for c in cards)
            choices = []
            for c in cards:
                hint = f"{human(c.size)} {c.kind} · {c.fs_label}" + ("   last used" if c.uuid and c.uuid == last else "")
                choices.append(option(c.name, c, hint, width=width, disabled=c.problem(changes=changes),
                                      description=f"{c.device} · {human(c.free)} free"))
            choices += [divider(), action_choice("Rescan", "rescan", "↻"), back()]
            first_ok = cards[0].problem(changes=changes) is None
            picked = ask_select("Which card?", choices, default=cards[0] if first_ok else "rescan")
            if picked is BACK:
                return None
            if picked == "rescan":
                continue

        contents = scan_card(picked.mount)
        show_card(picked, contents, state)
        right = ask_confirm("Is this the right card?", True, on_escape=BACK)
        if right is BACK:
            return None
        if right:
            RUN.confirmed = (picked.uuid, frozenset(c.uuid for c in cards)) if picked.uuid else None
            RUN.active = (picked, len(contents.albums))
            RUN.used[card_key(picked)] = picked
            return picked, contents
        if len(cards) == 1:
            warn("No other card found. Insert the right card, then pick Rescan.")
            if ask_select("No card", [action_choice("Rescan", "rescan", "↻"), back()]) is BACK:
                return None
        say()


def still_confirmed(cards: list[Card], *, changes: bool = True) -> Card | None:
    """The card confirmed earlier this run, if it and only the drives there then are still plugged in."""
    if RUN.confirmed is None or frozenset(c.uuid for c in cards) != RUN.confirmed[1]:
        return None
    card = next((c for c in cards if c.uuid == RUN.confirmed[0]), None)
    return card if card and card.problem(changes=changes) is None else None



# ── The library ───────────────────────────────────────────────────────────────

@dataclass
class Album:
    name: str
    path: Path
    tracks: list[Path]
    size: int


def scan_library(root: Path) -> list[Album]:
    """Albums are the folders directly inside the library; tracks are the audio files directly in each."""
    albums = []
    try:
        folders = [p for p in root.iterdir() if p.is_dir() and not p.name.startswith(".")]
    except OSError:
        return albums
    for folder in sorted(folders, key=lambda p: natural_key(p.name)):
        try:
            tracks = sorted(
                (p for p in folder.iterdir() if p.is_file() and not p.name.startswith(".") and is_audio(p)),
                key=lambda p: natural_key(p.name),
            )
            size = sum(t.stat().st_size for t in tracks)
        except OSError as error:  # e.g. a drive's root-only lost+found
            warn(f"Skipping {esc(folder.name)}: it can't be read ({esc(error.strerror or str(error))}).")
            continue
        if tracks:
            albums.append(Album(folder.name, folder, tracks, size))
    return albums


def fat_name_problems(albums: list[Album]) -> list[str]:
    """Names FAT and exFAT can't store, caught before anything is written: characters it can't hold, a name too
    long once a copy or rename puts it under a temporary name, or two names that differ only by case (fine on a
    Linux drive, but one would overwrite the other on the card)."""
    def bad(name: str) -> bool:
        return bool(FAT_BAD_NAME.search(name)) or utf16_length(name) > FAT_MAX_NAME - NAME_ROOM

    def same_on_card(names: list[str]) -> Counter:
        return Counter(nfc(name).casefold() for name in names)

    album_names = same_on_card([album.name for album in albums])
    found = []
    for album in albums:
        if bad(album.name) or album_names[nfc(album.name).casefold()] > 1:
            found.append(album.name)
        track_names = same_on_card([t.name for t in album.tracks])
        found += [f"{album.name}/{t.name}" for t in album.tracks
                  if bad(t.name) or track_names[nfc(t.name).casefold()] > 1]
    return found


def utf16_length(name: str) -> int:
    """A name's length as FAT and exFAT count it."""
    return len(name.encode("utf-16-le", errors="surrogatepass")) // 2


def library_places(state: dict) -> list[tuple[str, str]]:
    """Suggestions for a library folder: the last one used, then Music and Desktop."""
    places = [(tilde(state["library"]) + "/", "last used")] if state.get("library") else []
    return places + [(tilde(p) + "/", "") for p in (HOME / "Music", HOME / "Desktop") if p.is_dir()]


def ask_library(state: dict, message: str) -> tuple[Path, list[Album]] | None:
    """The library folder and its albums, or None to go back."""
    places = library_places(state)
    while True:
        default = tilde(state["library"]) if state.get("library") else ""
        library = ask_path(message, default, places, must_exist=True)
        if library is BACK:
            return None
        albums = scan_library(library)
        if albums:
            return library, albums
        warn("No albums there. An album is a folder of audio files inside the library folder.")



# ── Updating the card ─────────────────────────────────────────────────────────

@dataclass
class CopyJob:
    src: Path
    dst: Path
    size: int
    album: str


def copy_one(src: Path, dst: Path, on_bytes) -> None:
    """Copy under a temporary dot-name, then rename, so an interrupted copy never leaves half a track. Data
    only, though macOS still tags each new file, and writes a ._ file for it that cleaning removes."""
    temp = dst.with_name(f".{dst.name}.part")
    try:
        with open(src, "rb") as source, open(temp, "wb") as target:
            while chunk := source.read(1 << 20):
                target.write(chunk)
                on_bytes(len(chunk))
            durable(target)  # the data reaches the card before the name: Add trusts name and size
        if dst.exists():
            _clear_flags(dst)  # a track marked read-only (often ripped on Windows) can't be replaced otherwise
        os.replace(temp, dst)
        LOG.debug("   copied %s → %s", src, dst)
    except BaseException:
        temp.unlink(missing_ok=True)
        raise


def copy_tracks(plan: CopyPlan) -> None:
    per_album = Counter(job.album for job in plan.jobs)
    started = time.monotonic()
    with progress_bar() as bar:
        task = bar.add_task("", total=max(plan.copy_bytes, 1), detail="", note="")
        album, RUN.work = None, (0, len(plan.jobs))
        for number, job in enumerate(plan.jobs, 1):
            if job.album != album:
                album = job.album
                bar.console.print(Text.assemble(("│", "rail"), "  ", ("▸ ", "accent"), (album, "bold"),
                                                (f"  {plural(per_album[album], 'track')}", "hint")))
            bar.update(task, detail=f"{number}/{len(plan.jobs)} tracks", note=short(job.src.name))
            job.dst.parent.mkdir(exist_ok=True)
            copy_one(job.src, job.dst, lambda n: bar.advance(task, n))
            RUN.work = (number, len(plan.jobs))
    RUN.work = None
    elapsed = int(time.monotonic() - started)
    done(f"Copied {plural(len(plan.jobs), 'track')}, {human(plan.copy_bytes)} in {elapsed // 60}:{elapsed % 60:02d}")



# ── Card housekeeping ─────────────────────────────────────────────────────────
# Album and track names never start with a dot, so every dot-entry on the card is
# OS clutter. The purge and tidy helpers only remove dot-entries; erase_card (Replace everything)
# removes it all.

def same_filesystem(a: Path, b: Path) -> bool:
    try:
        return os.stat(a).st_dev == os.stat(b).st_dev
    except OSError:
        return False


def assert_card_root(card: Card) -> None:
    """Before every write to the card: still mounted, same device, same ID. Otherwise stop."""
    if not card_still_here(card):
        raise SafetyError(f"{card.mount} is no longer the card you picked ({card.name}).")


def _clear_flags(path: Path) -> None:
    if IS_MAC:
        run(["chflags", "-R", "nouchg,noschg,nohidden", str(path)])


def _remove(path: Path) -> None:
    """Delete a file or folder if it can be; the callers look again to find what stayed."""
    LOG.info("   remove %s", path)
    with suppress(OSError):
        if path.is_dir() and not path.is_symlink():
            shutil.rmtree(path)
        else:
            path.unlink()


def purge_hidden_top(root: Path) -> None:
    for entry in list(root.iterdir()):
        if entry.name.startswith("."):
            _clear_flags(entry)
            _remove(entry)


def purge_sidecars(root: Path) -> None:
    """._ AppleDouble files, .DS_Store, .apdisk and leftover .part files, anywhere on the card."""
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if not d.startswith(".")]
        for name in filenames:
            if name.startswith("._") or name in JUNK_FILES or partial_copy(name):
                LOG.debug("   remove %s", os.path.join(dirpath, name))
                with suppress(OSError):
                    os.unlink(os.path.join(dirpath, name))


def purge_clutter(root: Path, tools: Tools) -> None:
    """macOS's hidden files: ._ files merged away by dot_clean, any it left, and hidden top-level folders.
    Each step clears its own kind, so their order doesn't matter. A stopped rewrite's copy is settled first:
    it may be the only copy of its track."""
    settle_rewrites(root)
    if IS_MAC and tools.dot_clean:
        run(["dot_clean", "-m", str(root)])
    purge_sidecars(root)
    purge_hidden_top(root)


def prepare_card(card: Card, tools: Tools) -> None:
    """Clear clutter, then ask macOS to stop adding more while we copy.
    No `mdutil -i off`: it creates a protected .Spotlight-V100 that only Full Disk Access can delete."""
    assert_card_root(card)
    root = card.mount
    purge_clutter(root, tools)
    if IS_MAC:
        (root / ".metadata_never_index").touch()
        (root / ".fseventsd").mkdir(exist_ok=True)
        (root / ".fseventsd" / "no_log").touch()


def tidy_card(card: Card, tools: Tools, sudo: list[str] | None = None) -> list[str]:
    """Remove all clutter before the card goes back in the radio. Returns the hidden entries that wouldn't go."""
    assert_card_root(card)
    root = card.mount
    purge_clutter(root, tools)
    spotlight = root / ".Spotlight-V100"
    if IS_MAC and spotlight.exists() and sudo is not None:
        # Without Full Disk Access, Spotlight's own remover is the only way to delete its folder.
        run([*sudo, "mdutil", "-X", str(root)])
        for _ in range(10):
            if not spotlight.exists():
                break
            time.sleep(0.3)
    os.sync()
    return sorted(entry.name for entry in root.iterdir() if entry.name.startswith("."))


def erase_card(card: Card, tools: Tools) -> Card | None:
    """Replace everything: wipe the card. Delete in place with Full Disk Access, otherwise reformat."""
    assert_card_root(card)
    can_reformat = IS_MAC and card.fs in REFORMAT_AS and bool(card.device)

    if can_reformat and not tools.full_disk_access:
        with busy(f"Reformatting {esc(card.name)} as {card.fs_label}  [hint]Ctrl-C waits until it finishes[/]"):
            fresh = reformat(card)
        if fresh:
            done(f"Card reformatted: empty {fresh.fs_label}")
            return fresh
        warn("Reformatting didn't work, so deleting files instead.")

    assert_card_root(card)  # a failed reformat can leave a different volume, or none, at this path
    with busy(f"Erasing {esc(card.name)}"):
        for entry in list(card.mount.iterdir()):
            _clear_flags(entry)
            _remove(entry)
        os.sync()

    left = [e.name for e in card.mount.iterdir()]
    survivors = [n for n in left if n in PROTECTED_JUNK]
    if survivors and can_reformat:
        with busy("Reformatting to clear what macOS kept"):
            fresh = reformat(card)
        if fresh:
            done(f"Card reformatted: empty {fresh.fs_label}")
            return fresh
    visible = [n for n in left if not n.startswith(".")]
    if visible:
        fail(f"Couldn't erase {plural(len(visible), 'item')}, e.g. {esc(visible[0])}. Stopping.")
        return None
    if survivors:
        warn(f"Erased, but macOS kept {', '.join(survivors)}. Full Disk Access for your terminal clears them.")
    else:
        done("Card erased")
    return find_card(card.device, card.uuid) or card


def reformat(card: Card) -> Card | None:
    """Same format, same name, so the radio and the mount point see no difference."""
    if not device_still_matches(card):
        raise SafetyError(f"{card.device} no longer looks like {card.name}. Not reformatting it.")
    with ctrl_c_shield():
        result = run(["diskutil", "eraseVolume", REFORMAT_AS[card.fs], card.name, card.device], timeout=None)
    if result.returncode != 0:
        return None
    os.sync()
    for _ in range(10):
        if diskutil_info(card.device).get("MountPoint"):
            return find_card(card.device)
        run(["diskutil", "mount", card.device])
        time.sleep(0.5)
    # Erased, but not back: falling back to deleting files would only meet a card that isn't there
    raise SafetyError(f"{card.name} was reformatted and is now empty, but didn't mount again. "
                      "Plug it in again, then run Add.")



# ── Tracks stored in pieces ───────────────────────────────────────────────────
# The radio lists a track whose data lies in scattered pieces on the card, then skips it, though the file itself
# is fine. macOS's FAT and exFAT drivers give each file's first cluster as its inode number (checked on FAT32 and
# exFAT images), which allows two checks:
#   exact  the card's file table says where every piece of every track lies. FAT32 only, read from the device,
#          which on a real card takes the admin password.
#   quick  a track is surely in pieces when another file starts inside the run it would fill if it were whole.
#          No password, but it can only show that a track isn't whole, never that one is.
# macOS hands out the lowest free clusters first, so a track copied onto a card with gaps (left by deleted albums,
# or the ._ files cleaning removes) comes out in pieces. Asking macOS for one unbroken run (F_PREALLOCATE) changes
# nothing on its FAT driver, checked on images. So the gaps below the first run big enough are filled for a moment
# with a throwaway file, the track is written into that run, and the throwaway file goes: see soak_gaps.

FAT_ENTRY = 0x0FFFFFFF    # a FAT32 entry's low 28 bits name the next cluster; the top four are reserved
FAT_END = 0x0FFFFFF8      # this or higher ends a file's chain
REWRITE_SUFFIX = ".rewrite"  # a track's copy while it's rewritten, .~Name.rewrite: see settle_rewrite
SOAK = ".~soak"           # the throwaway file that fills the card's small gaps for a moment; cleaning removes a leftover
ROOM_PER_FILE = 2         # clusters a new file may take besides its data: macOS's ._ file for it, a folder growing


@dataclass
class FileTable:
    """A FAT32 card's file table: for each cluster, the next cluster of the file it belongs to."""
    cluster: int          # bytes per cluster
    entries: memoryview   # one 32-bit entry per cluster, from cluster 0
    last: int             # the highest cluster that holds data; entries past it are padding

    def pieces(self, first: int, size: int) -> int | None:
        """How many pieces a file of `size` bytes starting at cluster `first` lies in. None when its chain doesn't
        fit its size: then the table doesn't match the card, and nothing it says counts."""
        cluster, pieces = first, 1
        for _ in range(-(-size // self.cluster) - 1):  # never longer than the file, so a looped chain can't hang
            following = self.entries[cluster] & FAT_ENTRY if 2 <= cluster <= self.last else 0
            if not 2 <= following <= self.last:
                return None
            pieces += following != cluster + 1
            cluster = following
        ends = 2 <= cluster <= self.last and self.entries[cluster] & FAT_ENTRY >= FAT_END
        return pieces if ends else None

    def first_gap(self, clusters: int) -> tuple[int, int] | None:
        """The first run of at least `clusters` free clusters, by place on the card: where it starts, and how many
        free clusters lie before it, which macOS would fill first. None when no run is that long. A free entry is
        all zeros, so runs of zero bytes, trimmed to whole entries, are the gaps."""
        table = self.entries.tobytes()[8:(self.last + 1) * 4]  # clusters 2 to last
        before = 0
        for zeros in re.finditer(rb"\x00+", table):
            start, end = -(-zeros.start() // 4), zeros.end() // 4
            if end - start >= clusters:
                return start + 2, before
            before += max(0, end - start)
        return None

    def clusters_for(self, size: int) -> int:
        """Clusters a new file of `size` bytes takes, with room for what macOS adds beside it."""
        return -(-size // self.cluster) + ROOM_PER_FILE


def raw_device(card: Card) -> str:
    """macOS's raw node for the card's device, which reads in big blocks: /dev/rdisk5s1 for /dev/disk5s1."""
    return re.sub(r"^/dev/disk", "/dev/rdisk", card.device)


def read_device(device: str, offset: int, length: int, sudo: list[str]) -> bytes:
    """`length` bytes at `offset` from a device, through dd, under sudo when it's given. Both are whole sectors.
    Anything short of `length` comes back as b""."""
    block = math.gcd(offset, length, 1 << 20)
    result = run([*sudo, "dd", f"if={device}", f"bs={block}", f"skip={offset // block}", f"count={length // block}"],
                 binary=True, timeout=120)
    return result.stdout if result.returncode == 0 and len(result.stdout) == length else b""


def read_file_table(card: Card, sudo: list[str] | None) -> FileTable | None:
    """The card's FAT32 file table, read from its device while it's mounted: after a sync it's what macOS wrote
    (checked against images). None when it can't be read or doesn't look like the volume mounted there."""
    if sudo is None or not (IS_MAC and card.fs == "fat32" and card.device.startswith("/dev/disk")):
        return None
    os.sync()
    device = raw_device(card)
    boot = read_device(device, 0, 4096, sudo)
    if boot[510:512] != b"\x55\xaa":
        return None
    sector, per_cluster, reserved, copies = struct.unpack_from("<HBHB", boot, 0x0B)
    (small_total,), (small_table,) = struct.unpack_from("<H", boot, 0x13), struct.unpack_from("<H", boot, 0x16)
    big_total, table_sectors, flags = struct.unpack_from("<IIH", boot, 0x20)
    if (sector not in (512, 1024, 2048, 4096) or per_cluster not in (1, 2, 4, 8, 16, 32, 64, 128) or not copies
            or small_table or not table_sectors):  # FAT32 keeps its table size in the 32-bit field only
        return None
    try:
        if sector * per_cluster != os.statvfs(card.mount).f_frsize:
            return None  # not the volume mounted there
    except OSError:
        return None
    last = ((small_total or big_total) - reserved - copies * table_sectors) // per_cluster + 1
    active = flags & 0x0F if flags & 0x80 else 0  # with mirroring off, only the table it names is current
    if active >= copies or not 2 <= last or (last + 1) * 4 > table_sectors * sector:
        return None
    raw = read_device(device, (reserved + active * table_sectors) * sector, table_sectors * sector, sudo)
    return FileTable(sector * per_cluster, memoryview(raw).cast("I"), last) if raw else None


def tracks_in_pieces(root: Path, table: FileTable) -> dict[str, int] | None:
    """Each track in more than one piece, with how many. None when any track's chain doesn't fit its size."""
    found = {}
    for path in audio_files(root):
        try:
            info = path.stat()
        except OSError:
            return None
        if not info.st_size:
            continue  # an empty file has no cluster, so its inode number is made up
        pieces = table.pieces(info.st_ino, info.st_size)
        if pieces is None:
            return None
        if pieces > 1:
            found[path.relative_to(root).as_posix()] = pieces
    return found


def surely_in_pieces(tracks: dict[str, tuple[int, int]], starts: list[int], cluster: int) -> list[str]:
    """The tracks, given as name: (first cluster, size), that another file starts inside of: inside the run each
    would fill if it were whole. `starts` is every file's first cluster, sorted."""
    found = []
    for name, (first, size) in tracks.items():
        after = bisect.bisect_right(starts, first)
        if after < len(starts) and starts[after] < first + -(-size // cluster):
            found.append(name)
    return found


def quick_pieces(root: Path) -> list[str]:
    """Tracks surely stored in pieces, from inode numbers alone. Says nothing about the rest."""
    try:
        cluster = os.statvfs(root).f_frsize
    except OSError:
        return []
    starts, tracks = set(), {}
    for dirpath, _, filenames in os.walk(root):  # hidden folders too: their files take up room like any others
        for name in filenames:
            with suppress(OSError):
                if (info := os.lstat(os.path.join(dirpath, name))).st_size:
                    starts.add(info.st_ino)
    for path in audio_files(root):
        with suppress(OSError):
            if (info := path.stat()).st_size:
                tracks[path.relative_to(root).as_posix()] = (info.st_ino, info.st_size)
    return surely_in_pieces(tracks, sorted(starts), cluster)


def find_pieces(card: Card, sudo: list[str] | None) -> tuple[dict[str, int], FileTable | None]:
    """Tracks stored in pieces (name: pieces, 0 when not known), and the file table when the answer came from
    it, so that none found means none. Without the table, the quick check answers."""
    if not IS_MAC or card.fs not in FAT_FAMILY:
        return {}, None
    table = read_file_table(card, sudo)
    if table and (found := tracks_in_pieces(card.mount, table)) is not None:
        return found, table
    return dict.fromkeys(quick_pieces(card.mount), 0), None


def report_pieces(card: Card, found: dict[str, int], table: FileTable | None, sudo: list[str] | None, *,
                  quiet: bool = False) -> None:
    """What the search for tracks in pieces found. `quiet` (a routine clean): nothing said when only a quick check
    could run and it found none; Check is where that caveat belongs."""
    if found:
        warn(f"{plural(len(found), 'track')} stored in scattered pieces. The radio may skip "
             f"{'it' if len(found) == 1 else 'them'}:")
        listing([f"{name}  ({count} pieces)" if count else name for name, count in found.items()])
    elif table:
        done("Every track is stored in one piece")
    elif quiet:
        return
    elif not IS_MAC or card.fs not in FAT_FAMILY:
        say("[hint]Tracks stored in pieces can only be found on macOS.[/]")
    else:
        why = ("on exFAT, that's the only check there is" if card.fs == "exfat"
               else "only a FAT32 card's file table can be read" if card.fs != "fat32"
               else "the full check needs your password" if sudo is None
               else "the card's file table couldn't be read")
        say(f"[hint]A quick check found no tracks stored in pieces, though it can't rule them out: {why}.[/]")


def rebuild_hint() -> None:
    say("[hint]To rebuild the card with every track in one piece: back up the card, restore that backup into a "
        "folder, then use Add albums › Replace everything with it.[/]")


def settle_rewrite(copy: Path) -> Path | None:
    """A copy a rewrite left: deleted when its track is there, otherwise put in the track's place, since it may
    be the only copy. Returns the track when it was put back."""
    track = copy.with_name(copy.name.removeprefix(".~").removesuffix(REWRITE_SUFFIX))
    if track.exists():
        LOG.info("   remove %s, as its track is there", copy)
        copy.unlink(missing_ok=True)
        return None
    LOG.info("   put back %s as %s", copy, track)
    os.replace(copy, track)
    return track


def settle_rewrites(root: Path) -> None:
    """Copies a stopped rewrite left anywhere on the card: see settle_rewrite."""
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if not d.startswith(".")]
        for name in filenames:
            if name.startswith(".~") and name.endswith(REWRITE_SUFFIX):
                with suppress(OSError):  # by the spelling it was written under, which macOS can rename
                    if track := settle_rewrite(root / written(os.path.relpath(os.path.join(dirpath, name), root))):
                        warn(f"Put back {esc(_relative(track, root))} from a stopped rewrite, as it was the only copy. "
                             "Check › Find damaged tracks can test it.")


def soak_gaps(card: Card, table: FileTable, clusters: int) -> Path | None:
    """Fill the free clusters below the first gap that holds `clusters` with one hidden file at the card's top, so
    what's written next lands in that gap in one piece: macOS hands out the lowest free clusters first (checked on
    images). Returns the file, to delete once that's written; None when nothing needed filling."""
    gap = table.first_gap(clusters)
    if gap is None or not gap[1]:
        return None
    soak = card.mount / SOAK
    zeros, left = bytes(1 << 20), gap[1] * table.cluster
    try:
        with open(soak, "wb") as out:
            while left:
                left -= out.write(zeros[:min(left, len(zeros))])
            out.flush()
            os.fsync(out.fileno())
    except BaseException:  # a full card or a Ctrl-C partway: never leave gigabytes of zeros behind
        soak.unlink(missing_ok=True)
        raise
    return soak


@contextmanager
def landing_whole(card: Card, sudo: list[str] | None, sizes: list[int]):
    """While new tracks are copied: the card's small gaps filled, so each lands in one piece. Without the file
    table, or with no gap big enough for them all, they're copied as they come, and the check afterwards finds any
    in pieces."""
    assert_card_root(card)  # the password prompt just before this can outlast the card, or see it swapped
    table = read_file_table(card, sudo)
    soak = None
    if table:
        with busy("Filling the card's small gaps, so each track lands in one piece"), suppress(OSError):
            soak = soak_gaps(card, table, sum(map(table.clusters_for, sizes)) + ROOM_PER_FILE)
    try:
        yield
    finally:
        if soak:
            soak.unlink(missing_ok=True)


def rewrite_whole(card: Card, name: str, sudo: list[str], table: FileTable, on_bytes) -> str | None:
    """Copy a track into the first gap on the card that holds it whole (the gaps before it filled for a moment),
    check that the copy reads back the same and lies in one piece, then let it take the original's place. Returns
    why it didn't, or None. The original is only ever replaced by a copy that passed both checks."""
    assert_card_root(card)
    path = card.mount / written(name)  # the composed spelling: macOS can't rename a copy made under the other
    copy = path.with_name(f".~{path.name}{REWRITE_SUFFIX}")  # never "._…", which cleaning takes for macOS's
    info = path.stat()
    soak = None
    try:
        soak = soak_gaps(card, table, table.clusters_for(info.st_size) + ROOM_PER_FILE)
        original = hashlib.sha256()
        with open(path, "rb") as source, open(copy, "wb") as target:
            fcntl.fcntl(target.fileno(), fcntl.F_NOCACHE, 1)  # not kept in RAM: the read-back has to read the card
            while chunk := source.read(1 << 20):
                original.update(chunk)
                target.write(chunk)
                on_bytes(len(chunk))
            durable(target)
        with open(copy, "rb") as written_copy:
            fcntl.fcntl(written_copy.fileno(), fcntl.F_NOCACHE, 1)
            if _sha256(written_copy, lambda n: None) != original.hexdigest():
                return "the copy read back differently"
        after = read_file_table(card, sudo)
        pieces = after.pieces(os.stat(copy).st_ino, info.st_size) if after else None
        if pieces != 1:
            return "the copy landed in pieces too" if pieces else "the copy couldn't be checked"
        os.utime(copy, ns=(info.st_atime_ns, info.st_mtime_ns))
        os.replace(copy, path)
        return None
    except OSError as error:
        return error.strerror or str(error)
    finally:
        with suppress(OSError):
            if copy.exists():
                settle_rewrite(copy)
        if soak:
            soak.unlink(missing_ok=True)


def mend_pieces(card: Card, sudo: list[str] | None, *, sortable: bool = True) -> tuple[int, int]:
    """Find tracks stored in pieces and offer to rewrite each in one piece. Returns how many were rewritten, and
    how many are known to be left in pieces. A rewritten track takes a new place in its folder's list, so only a
    card fatsort can sort afterwards is rewritten."""
    found, table = find_pieces(card, sudo)
    report_pieces(card, found, table, sudo, quiet=True)
    if not found:
        return 0, 0
    if table is None:
        say("[hint]Rewriting needs the card's file table to check each copy: FAT32 on macOS, with your password.[/]")
        rebuild_hint()
        return 0, len(found)
    if not sortable:
        say("[hint]A rewritten track moves in its folder's play order until fatsort sorts the card, and fatsort "
            "can't here (see below), so they're left as they are.[/]")
        return 0, len(found)
    try:
        sizes = {name: (card.mount / name).stat().st_size for name in found}
    except OSError as error:
        warn(f"Left in pieces: the card couldn't be read ({esc(error.strerror or str(error))}).")
        return 0, len(found)
    say(f"[hint]Each is copied to an unbroken spot on the card, read back and checked against the original, then "
        f"takes its place. {human(sum(sizes.values()))} to copy, plus a throwaway file that fills the card's small "
        "gaps meanwhile; play order and names stay as they are.[/]")
    if not ask_confirm(f"Rewrite {'it' if len(found) == 1 else 'them'} in one piece?", True):
        warn(f"Left in pieces. The radio may skip {'it' if len(found) == 1 else 'them'}.")
        return 0, len(found)
    if (sudo := keep_admin(sudo, ask=True)) is None:  # the question may have outlasted sudo's grace
        warn("Left in pieces: without admin rights, no copy could be checked.")
        return 0, len(found)

    left = []
    with progress_bar() as bar:
        task = bar.add_task("", total=max(sum(sizes.values()), 1), detail="", note="")
        for number, name in enumerate(found, 1):
            bar.update(task, detail=f"{number}/{len(found)} tracks", note=short(Path(name).name))
            if keep_admin(sudo) is None:  # sudo's grace ran out: a copy now couldn't be checked
                why = "admin rights ran out, so it wasn't copied"
            elif (table := read_file_table(card, sudo)) is None:  # read afresh: the last rewrite freed clusters
                why = "the card's file table couldn't be read again"
            elif table.first_gap(table.clusters_for(sizes[name]) + ROOM_PER_FILE) is None:
                why = "no gap on the card is big enough for it"
            else:
                why = rewrite_whole(card, name, sudo, table, lambda n: bar.advance(task, n))
            LOG.info("   rewrite %s: %s", name, why or "whole now")
            if why:
                left.append(f"{name}: {why}")
            bar.update(task, completed=sum(sizes[n] for n in list(found)[:number]))
    rewritten = len(found) - len(left)
    if rewritten:
        done(f"Rewrote {plural(rewritten, 'track')}, each now in one piece")
    if left:
        warn(f"{plural(len(left), 'track')} still in pieces:")
        listing(left)
        rebuild_hint()
    return rewritten, len(left)



# ── Play order: fatsort ───────────────────────────────────────────────────────

def fatsort_key(name: str) -> list[tuple[int, int]]:
    """The order fatsort -n -c gives (checked on FAT32 images): a run of digits counts as its number, so 2
    comes before 10, and sorts before any ASCII character; ASCII letters ignore case; and anything beyond
    ASCII comes first of all, since fatsort compares UTF-8 bytes as signed chars. Only ASCII digits make a
    number, as in fatsort's byte compare; "²" or "٣" are bytes like any other. Names that aren't UTF-8 (on Linux)
    compare by the bytes they're stored as."""
    key = []
    for part in re.split(r"([0-9]+)", nfc(name)):
        if part.isascii() and part.isdigit():
            key.append((0, int(part)))
        else:
            key += [(b - 256 if b > 127 else b + 32 if 65 <= b <= 90 else b, 0)
                    for b in part.encode(errors="surrogateescape")]
    return key


def visible_tree(root: Path) -> dict[str, list[str]]:
    """The order fatsort should produce: per folder, subfolders then files."""
    tree = {}
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = sorted((d for d in dirnames if not d.startswith(".")), key=fatsort_key)
        files = sorted((f for f in filenames if not f.startswith(".")), key=fatsort_key)
        relative = os.path.relpath(dirpath, root)
        tree["" if relative == "." else relative] = dirnames + files
    return tree


# macOS keeps characters FAT can't hold (" * : < > ? \ | and a trailing space or dot) on the card as
# stand-ins U+F020–U+F029, and shows the real ones when it lists a folder. fatsort prints the stand-ins,
# so its names are translated back before comparing: "Exile On Main St" + U+F029 is "Exile On Main St.".
MAC_STAND_INS = str.maketrans({0xF020 + i: c for i, c in enumerate('"*:<>?\\| .')}
                              | {0xF000 + i: chr(i) for i in range(1, 0x20)})


def parse_fatsort_listing(text: str) -> dict[str, list[str]]:
    """`fatsort -l` prints each directory as /path/ followed by its entries in on-card order."""
    order, current = {}, None
    for line in text.splitlines():
        line = line.translate(MAC_STAND_INS)
        if line.startswith("/") and line.endswith("/"):
            current = line.strip("/")
            order[current] = []
        elif current is not None and line and line not in (".", ".."):
            order[current].append(line)
    return order


@dataclass
class OrderProblem:
    folder: str      # "" is the top of the card: the album order
    detail: str
    sortable: bool   # False when the names themselves don't match, which sorting can't settle


def order_problems(expected: dict[str, list[str]], actual: dict[str, list[str]]) -> list[OrderProblem]:
    """Each folder whose on-card order isn't the expected one, with what's wrong in plain words."""
    problems = []
    # fatsort prints names composed, and 8.3 ones in capitals; macOS lists them decomposed. FAT ignores case.
    actual = {nfc(folder).casefold(): names for folder, names in actual.items()}
    for folder, names in expected.items():
        want = [nfc(n) for n in names]
        if nfc(folder).casefold() not in actual:
            problems.append(OrderProblem(folder, "couldn't read this folder's order", False))
            continue
        spelled = {n.casefold(): n for n in want}
        on_card = [spelled.get(nfc(n).casefold(), nfc(n)) for n in actual[nfc(folder).casefold()] if not n.startswith(".")]
        if on_card == want:
            continue
        if sorted(on_card) != sorted(want):
            odd = [n for n in on_card if n not in want] or [n for n in want if n not in on_card]
            problems.append(OrderProblem(folder, f"a name reads differently from what macOS shows: {odd[0]}", False))
            continue
        first = next(i for i, (have, should) in enumerate(zip(on_card, want)) if have != should)
        problems.append(OrderProblem(folder, f"{on_card[first]} plays before {want[first]}", True))
    return problems


def show_order_problems(problems: list[OrderProblem], limit: int = 6) -> None:
    for problem in problems[:limit]:
        where = problem.folder or "Album order"
        say(f"  [strong]{esc(where)}[/]: {esc(problem.detail)}")
    if len(problems) > limit:
        say(f"  [hint]… {len(problems) - limit} more folders[/]")


def sort_blocker(card: Card, tools: Tools) -> str | None:
    if not tools.fatsort:
        return f"fatsort isn't installed, so play order can't be fixed ({install_hint('fatsort')})."
    if card.fs not in FAT_FAMILY:
        return "The card isn't FAT or exFAT, so fatsort can't sort it."
    if card.fs == "exfat" and tools.fatsort_version < (1, 7):
        found = ".".join(map(str, tools.fatsort_version)) or "an unknown version"
        upgrade = "brew upgrade fatsort" if IS_MAC else "Debian and Ubuntu ship 1.6; get 1.7 from fatsort.sourceforge.io"
        return f"This fatsort is {found}. Sorting exFAT needs 1.7 or newer ({upgrade})."
    if not card.device or not card.uuid:
        return "Couldn't identify the card's device, so it won't be sorted."
    return None


def manual_sort_hint(card: Card) -> None:
    flags = " ".join(FATSORT_FLAGS)
    mount, device, whole = (shlex.quote(str(part)) for part in (card.mount, card.device, card.whole))
    if IS_MAC:
        command = f"diskutil unmount {mount} && sudo fatsort {flags} {device} && diskutil eject {whole}"
    else:
        command = f"udisksctl unmount -b {device} && sudo fatsort {flags} {device}"
    say("[hint]To sort it yourself later:[/]")
    say(f"  {esc(command)}")


class Interrupted(KeyboardInterrupt):
    """A stop by signal (SIGTERM, a closed terminal), handled as Ctrl-C is, so every cleanup on the way out runs."""

    def __init__(self, signum: int):
        super().__init__(signum)
        self.signum = signum


def stop_on_signal(signum: int, frame) -> None:
    raise Interrupted(signum)


@contextmanager
def ctrl_c_shield():
    """While the card's file table is rewritten, Ctrl-C, Ctrl-Z, a closed terminal and SIGTERM can't cut in:
    stopping halfway could scramble the card. Ctrl-Z and a closed terminal are ignored, and a command running
    then inherits that. A Ctrl-C pressed meanwhile is read as a key, and SIGTERM, sent to this process alone,
    is noted; either stops the run afterwards."""
    fd = sys.stdin.fileno() if sys.stdin is not None and sys.stdin.isatty() else None
    saved_tty = termios.tcgetattr(fd) if fd is not None else None
    noted = []
    saved = {sig: signal.signal(sig, signal.SIG_IGN) for sig in (signal.SIGINT, signal.SIGTSTP, signal.SIGHUP)}
    saved[signal.SIGTERM] = signal.signal(signal.SIGTERM, lambda signum, frame: noted.append(signum))
    pressed = b""
    try:
        if saved_tty:
            quiet = termios.tcgetattr(fd)
            quiet[3] &= ~(termios.ISIG | termios.ICANON | termios.ECHO)  # ^C arrives as a byte, readable at once
            quiet[6][termios.VMIN], quiet[6][termios.VTIME] = 0, 0
            termios.tcsetattr(fd, termios.TCSANOW, quiet)
        yield
    finally:
        if saved_tty:
            with suppress(OSError):
                while chunk := os.read(fd, 1024):
                    pressed += chunk
            termios.tcflush(fd, termios.TCIFLUSH)  # keys typed meanwhile can't answer the next prompt
            termios.tcsetattr(fd, termios.TCSANOW, saved_tty)
        for sig, handler in saved.items():
            signal.signal(sig, handler)
    if noted:
        raise Interrupted(noted[0])
    if b"\x03" in pressed:
        raise KeyboardInterrupt


def unmount_card(card: Card, sudo: list[str]) -> bool:
    os.sync()
    if IS_MAC:
        if run(["diskutil", "unmount", str(card.mount)]).returncode == 0:
            return True
        return run(["diskutil", "unmountDisk", card.whole]).returncode == 0
    if shutil.which("udisksctl") and run(["udisksctl", "unmount", "--no-user-interaction", "-b", card.device]).returncode == 0:
        return True
    return run([*sudo, "umount", str(card.mount)]).returncode == 0


def can_mount() -> bool:
    """Whether an unmounted card can be mounted again from here: diskutil on macOS, udisks2 on Linux."""
    return IS_MAC or bool(shutil.which("udisksctl"))


def mount_card(card: Card) -> bool:
    if IS_MAC:
        return run(["diskutil", "mount", card.device]).returncode == 0
    if not can_mount():
        return False
    return run(["udisksctl", "mount", "--no-user-interaction", "-b", card.device]).returncode == 0


def eject_card(card: Card) -> bool:
    """Eject the whole card. On Linux, unmounted is already safe to pull; power-off is a bonus."""
    os.sync()
    if IS_MAC:
        ok = run(["diskutil", "eject", card.whole or str(card.mount)]).returncode == 0
    else:
        if os.path.ismount(card.mount):
            unmount_card(card, ["sudo", "-n"])
        ok = not os.path.ismount(card.mount)
        if ok and shutil.which("udisksctl"):
            run(["udisksctl", "power-off", "--no-user-interaction", "-b", card.whole])
    if ok:  # an ejected card is confirmed again if it comes back
        RUN.active = RUN.card_in_use = RUN.confirmed = None
        RUN.used.pop(card_key(card), None)
    return ok


def get_admin(card: Card, tools: Tools, *, sorting: bool = True, spotlight: bool = True) -> list[str] | None:
    """One password for whatever is ahead: fatsort on a device we can't write, Spotlight's protected folder, and
    reading the file table to find tracks stored in pieces. Returns the sudo prefix ([] when nothing needs it), or
    None when admin rights were refused."""
    sorting = sorting and sort_blocker(card, tools) is None and not os.access(card.device, os.W_OK)
    spotlight = spotlight and IS_MAC and not tools.full_disk_access and (card.mount / ".Spotlight-V100").exists()
    reading = IS_MAC and card.fs == "fat32" and bool(card.device) and not os.access(raw_device(card), os.R_OK)
    needs = (["fatsort"] if sorting else []) + (["removing Spotlight's folder"] if spotlight else []) \
        + (["checking for tracks stored in pieces"] if reading else [])
    if not needs:
        return []
    listed = needs[0] if len(needs) == 1 else ", ".join(needs[:-1]) + " and " + needs[-1]
    say(f"{listed[0].upper()}{listed[1:]} need{'s' if len(needs) == 1 else ''} admin rights. "
        "You may be asked for your password.")
    if run(["sudo", "-v"], interactive=True).returncode != 0:
        warn("No admin rights.")
        return None
    return ["sudo", "-n"]


def keep_admin(sudo: list[str] | None, *, ask: bool = False) -> list[str] | None:
    """Keep sudo's few minutes of grace from running out during a long step. Once they have, `ask` asks for the
    password again; without it, or when that's refused, the rights are gone (None)."""
    if not sudo or run([*sudo, "-v"]).returncode == 0:
        return sudo
    if ask:
        say("Admin rights ran out. You may be asked for your password again.")
        if run(["sudo", "-v"], interactive=True).returncode == 0:
            return sudo
        warn("No admin rights.")
    return None


def take_card_offline(card: Card, sudo: list[str]) -> bool:
    """Unmount, then check the device is still the card the user picked."""
    if not unmount_card(card, sudo):
        warn("Couldn't unmount the card. Close any window showing it, then try again.")
        manual_sort_hint(card)
        return False
    if not device_still_matches(card):
        raise SafetyError(f"{card.device} no longer looks like {card.name}. Not touching it.")
    return True


def run_fatsort(card: Card, sudo: list[str]) -> bool:
    with ctrl_c_shield(), busy("Sorting with fatsort  [hint]Ctrl-C waits until it finishes[/]"):
        result = run([*sudo, "fatsort", *FATSORT_FLAGS, card.device], timeout=None)
    if result.returncode != 0:
        detail = (result.stderr or result.stdout).strip().splitlines()
        if detail and detail[-1].startswith("sudo:"):  # the admin rights asked for earlier ran out
            warn("sudo didn't let fatsort run, so the card wasn't sorted.")
        else:
            warn("fatsort reported a problem. The files are on the card, but the order may be off.")
        if detail:
            say(f"[hint]{esc(detail[-1])}[/]")
        return False
    return True


def listed_order(root: Path) -> dict[str, list[str]]:
    """The order macOS lists each folder in, keyed like `fatsort -l`. On FAT and exFAT that's the order the
    entries sit on the card (checked against fatsort -l), so reading it needs no unmount."""
    order, folders = {}, [""]
    while folders:
        folder = folders.pop()
        try:
            entries = list(os.scandir(root / folder))
        except OSError:
            continue
        order[folder] = [entry.name for entry in entries]
        folders += [os.path.join(folder, entry.name) for entry in entries
                    if entry.is_dir(follow_symlinks=False) and not entry.name.startswith(".")]
    return order


def read_order(card: Card, sudo: list[str]) -> dict[str, list[str]]:
    with busy("Reading the play order back"):
        result = run([*sudo, "fatsort", "-l", card.device], timeout=None)
    return parse_fatsort_listing(result.stdout) if result.returncode == 0 else {}


def report_order(expected: dict[str, list[str]], actual: dict[str, list[str]], *, after_sort: bool) -> list[OrderProblem]:
    """Say whether the card plays in the expected order, and if not, which folders and why."""
    if not actual:
        warn("Couldn't read the order from the card.")
        return [OrderProblem("", "no order could be read", False)]
    problems = order_problems(expected, actual)
    albums = sum(1 for folder in expected if folder and "/" not in folder and folder.casefold() not in WINDOWS_DIRS)
    if not problems:
        done(f"Sorted, then read back: {plural(albums, 'album')} in order" if after_sort else "Everything is in order")
    elif after_sort:
        warn(f"After sorting, {plural(len(problems), 'folder')} still differ{'s' if len(problems) == 1 else ''} "
             "from what was expected:")
        show_order_problems(problems)
    elif all(p.sortable for p in problems):
        warn(f"{plural(len(problems), 'folder')} out of play order:")
        show_order_problems(problems)
    else:
        warn(f"{plural(len(problems), 'folder')} don't match what was expected:")
        show_order_problems(problems)
        say("[hint]Sorting never renames, so it can't settle names that read differently.[/]")
    return problems


def sort_card(card: Card, tools: Tools, expected: dict[str, list[str]], sudo: list[str] | None) -> bool:
    """Unmount, fatsort, read the order back. True only when the order on the card is confirmed."""
    blocker = sort_blocker(card, tools)
    if blocker or sudo is None:
        warn(blocker or "No admin rights, so the card wasn't sorted.")
        manual_sort_hint(card)
        return False
    if not take_card_offline(card, sudo):
        return False
    return run_fatsort(card, sudo) and not report_order(expected, read_order(card, sudo), after_sort=True)



# ── Album numbers ─────────────────────────────────────────────────────────────
# fatsort orders the card by name, so a number at the front holds each album's place:
# "01 - The Beach Boys - Pet Sounds". Inserting, moving or deleting an album renumbers the rest 1..N.
# Renaming a folder on the card moves no audio, so rearranging takes seconds.

LEADING_NUMBER = re.compile(r"^(\d+)(\s*[-–—.]\s*|\s+|_)(.+)$")


@dataclass(frozen=True)
class Numbering:
    """How a card numbers its albums: digits and separator, e.g. 2 and " - " for "01 - Pet Sounds".
    On a card that separates with punctuation, a title that only starts with digits ("50 Cent - …",
    "1999 Remaster") is never mistaken for a number, so renumbering can't eat part of a name."""
    width: int = 2
    separator: str = " - "

    @classmethod
    def of(cls, names: list[str]) -> Numbering:
        """The style most of these names use. Two digits at least, so names also sort right as plain text.
        When any name separates with punctuation, only those count: "50 Cent - …" says nothing about style."""
        found = [m for m in map(LEADING_NUMBER.match, names) if m]
        found = [m for m in found if not m.group(2).isspace()] or found
        if not found:
            return cls()
        widths = [len(m.group(1)) for m in found]
        separators = [m.group(2) for m in found]
        return cls(max(2, Counter(widths).most_common(1)[0][0]), Counter(separators).most_common(1)[0][0])

    def split(self, name: str) -> tuple[str, str, str]:
        """A folder name's number as written, its separator and its title. No number: ("", "", name)."""
        match = LEADING_NUMBER.match(name)
        if not match or (match.group(2).isspace() and not self.separator.isspace()):
            return "", "", name
        return match.groups()

    def number(self, name: str) -> int | None:
        digits = self.split(name)[0]
        return int(digits) if digits else None

    def title(self, name: str) -> str:
        return self.split(name)[2]

    def album_key(self, name: str) -> str:
        """An album's identity without its number, so "03 - Beck" and "04 - Beck" are the same album."""
        return nfc(self.title(name)).casefold()

    def renumber(self, order: list[str], titles: dict[str, str] | None = None) -> dict[str, str]:
        """Every album in `order`, in play order, named with its place as the number. Its own separator
        and title stay, unless `titles` gives it a new title."""
        width = max(self.width, len(str(len(order))))
        final = {}
        for place, name in enumerate(order, 1):
            _, separator, title = self.split(name)
            final[name] = f"{place:0{width}d}{separator or self.separator}{(titles or {}).get(name, title)}"
        return final

    def renames(self, order: list[str], titles: dict[str, str] | None = None) -> list[tuple[str, str]]:
        """Only the albums whose name changes."""
        return [(old, new) for old, new in self.renumber(order, titles).items() if nfc(old) != nfc(new)]


def show_renames(renames: list[tuple[str, str]], numbering: Numbering, limit: int = 10) -> None:
    for old, new in renames[:limit]:
        old_number, _, old_title = numbering.split(old)
        new_number, _, new_title = numbering.split(new)
        old_number = old_number or "--"
        say(f"  [hint]{old_number} →[/] {new_number}  {esc(new_title)}")
        if old_title != new_title:
            say(f"  [hint]{' ' * (len(old_number) + len(new_number) + 5)}was {esc(old_title)}[/]")
    if len(renames) > limit:
        say(f"  [hint]… {len(renames) - limit} more[/]")


def check_title(title: str, full_name: str, other_titles: set[str]) -> tuple[str | None, str | None]:
    """A new album title: a reason to refuse it, or a caution to confirm first."""
    if not title:
        return "A name can't be empty.", None
    if title.startswith("."):
        return "A name can't start with a dot: Clean would treat the album as hidden clutter.", None
    if "/" in title:
        return "A name can't contain a slash.", None
    if "\0" in title:
        return "A name can't contain a NUL character.", None
    if utf16_length(full_name) > FAT_MAX_NAME - NAME_ROOM:  # as FAT counts, with room for the name while renaming
        return (f"That's too long for the card: {FAT_MAX_NAME - NAME_ROOM} characters at most, number included.",
                None)
    if nfc(title).casefold() in other_titles:
        return "Another album on the card already has that name.", None
    if FAT_BAD_NAME.search(full_name):
        return None, ('FAT cards can\'t hold " * : < > ? \\ | or a trailing dot or space. macOS stores '
                      "stand-ins for them, which the radio may show oddly.")
    return None, None


def ask_title(name: str, order: list[str], numbering: Numbering, titles: dict[str, str]) -> str | None:
    """Ask for an album's new title, the number left out. None when it stays as it is."""
    current = titles.get(name, numbering.title(name))
    others = {nfc(titles.get(n, numbering.title(n))).casefold() for n in order if n != name}
    while True:
        typed = ask_text("New name, without the number:", default=current)
        if typed is BACK:
            return None
        typed = typed.strip()
        if nfc(typed) == nfc(current):  # the same title, maybe spelled with accents composed differently
            say("[hint]Name unchanged.[/]")
            return None
        refuse, caution = check_title(typed, numbering.renumber(order, titles | {name: typed})[name], others)
        if refuse:
            warn(refuse)
            continue
        if caution:
            warn(caution)
            if not ask_confirm("Use it anyway?", False):
                continue
        return typed


def apply_renames(root: Path, renames: list[tuple[str, str]]) -> None:
    """Rename album folders on the card. A new name can match another album's old one, so anything that
    would collide waits under a temporary, visible name: a hidden one could be mistaken for clutter."""
    finals = [nfc(new).casefold() for _, new in renames]
    if len(set(finals)) != len(finals):
        raise SafetyError("Two albums would end up with the same name. Nothing was renamed.")
    taken = {nfc(name).casefold() for name in os.listdir(root)} | set(finals)

    def parking(old: str) -> str:
        """A temporary name nothing has, even one a killed run left behind. It only has to be unique, so a name
        already near FAT's limit (Finder allows longer ones than this script) is cut short to leave room."""
        stem = old
        while utf16_length(stem) > FAT_MAX_NAME - NAME_ROOM:
            stem = stem[:-1]
        for number in itertools.count(1):
            temp = f"{stem} (renaming)" if number == 1 else f"{stem} (renaming {number})"
            if nfc(temp).casefold() not in taken:
                taken.add(nfc(temp).casefold())
                return temp

    parked = []
    for old, new in renames:
        LOG.info("   rename %s → %s", old, new)
        if (root / new).exists():
            temp = root / written(parking(old))
            os.rename(root / written(old), temp)
            parked.append((temp, new))
        else:
            os.rename(root / written(old), root / written(new))
    for temp, new in parked:
        os.rename(temp, root / written(new))


def remove_album(card: Card, name: str) -> None:
    folder = card.mount / name
    if name.startswith(".") or name.casefold() in WINDOWS_DIRS or folder.parent != card.mount or not folder.is_dir() or folder.is_symlink():
        raise SafetyError(f"{name} isn't an album folder on the card.")
    LOG.info("   delete %s", folder)
    _clear_flags(folder)  # macOS shows FAT's read-only mark as a lock flag, which would stop the delete halfway
    shutil.rmtree(folder)


def pick_album(order: list[str], message: str):
    """An album's name, or BACK."""
    return ask_select(message, [*(option(name, name, plain=True) for name in order), *([divider()] if order else []),
                                back()], search=True)


def pick_place(order: list[str], message: str, default: int):
    """Where to put an album among `order`: an index into it, or BACK."""
    choices = [option("First", 0, plain=True)] + [option(f"After {name}", i + 1, plain=True)
                                                  for i, name in enumerate(order)] + [divider(), back()]
    return ask_select(message, choices, default=min(default, len(order)), search=True)



# ── Task: add albums ──────────────────────────────────────────────────────────

def repeated_titles(library: list[str], on_card: list[str]) -> list[str]:
    """Titles that two albums share, in the folder or on the card: matching by title can't tell them apart.
    Each is named as it appears, with "on the card" when that's where. The folder's titles are read in the style
    Add matches by (the card's), so "01 - Foo" and "02 Foo" are caught when both would match one album there."""
    twice = []
    matching = Numbering.of(on_card or library)
    for names, where, numbering in ((library, "", matching), (on_card, " (on the card)", Numbering.of(on_card))):
        seen = Counter(numbering.album_key(name) for name in names)
        twice += sorted({numbering.title(name) + where for name in names if seen[numbering.album_key(name)] > 1})
    return twice


def match_albums(albums: list[Album], on_card: list[str], numbering: Numbering) -> tuple[dict[str, str], list[Album]]:
    """Which albums are already on the card (by title, whatever their number), and which are new."""
    card_albums = {numbering.album_key(name): name for name in on_card}
    matched, new = {}, []
    for album in albums:
        card_name = card_albums.get(numbering.album_key(album.name))
        if card_name:
            matched[album.name] = card_name
        else:
            new.append(album)
    return matched, new


def default_place(name: str, order: list[str], on_card: set[str], numbering: Numbering) -> tuple[int, str | None]:
    """Where a new album goes by its number: before the first album numbered higher. If an album already
    on the card has the same number, that album comes back too, so the user can choose. No number: the end."""
    number = numbering.number(name)
    if number is None:
        return len(order), None
    for index, other in enumerate(order):
        other_number = numbering.number(other)
        if other_number is None or other_number > number:
            return index, None
        if other_number == number and other in on_card:
            return index, other
    return len(order), None


def place_new_albums(new: list[Album], order: list[str], numbering: Numbering):
    """Slot each new album in by its number, asking only when an album on the card already has it.
    The new order, or BACK."""
    on_card = set(order)
    order = list(order)
    for album in sorted(new, key=lambda a: natural_key(a.name)):
        place, taken_by = default_place(album.name, order, on_card, numbering)
        if taken_by:
            title = numbering.title(taken_by)
            say(f"New: [strong]{esc(album.name)}[/]")
            warn(f"Number {numbering.split(album.name)[0]} is taken by {esc(title)}")
            with doing("Placing", nfc(album.name)):
                while True:
                    choice = ask_select("Where should it go?", [
                        option(f"Before {title}", place, "it and the albums after it move down one"),
                        option("At the end", len(order)),
                        option("Somewhere else…", "else"),
                        back(),
                    ])
                    if choice is BACK:
                        return BACK
                    picked = pick_place(order, "Put it where?", place) if choice == "else" else choice
                    if picked is not BACK:
                        place = picked
                        break
        order.insert(place, album.name)
    return order


@dataclass
class CopyPlan:
    renames: list[tuple[str, str]]
    jobs: list[CopyJob]
    new_albums: list[str]
    changed_albums: list[str]
    same_albums: list[str]
    copy_bytes: int
    replaced_bytes: int


def plan_copy(albums: list[Album], card_root: Path, final: dict[str, str], on_card: set[str],
              matched: dict[str, str]) -> CopyPlan:
    """What changes on the card. `final` maps every album, in play order, to its folder name afterwards;
    `on_card` holds the folders there now; `matched` points source albums at the card folder that already
    holds them. A track already on the card with the same name and size isn't copied again."""
    plan = CopyPlan([(n, f) for n, f in final.items() if n in on_card and n != f], [], [], [], [], 0, 0)
    source = {matched.get(album.name, album.name): album for album in albums}
    for name, target in final.items():
        album = source.get(name)
        if album is None:
            continue
        before = len(plan.jobs)
        # The card's own spelling of each track. Linux's FAT driver treats the two Unicode forms of a name as two
        # names, so a track macOS wrote composed would otherwise be copied again beside itself.
        stored = {}
        if name in on_card:
            with suppress(OSError):
                stored = {nfc(entry): entry for entry in os.listdir(card_root / name)}
        for track in album.tracks:
            size = track.stat().st_size
            spelling = stored.get(nfc(track.name), track.name)
            existing = card_root / name / spelling
            if name in on_card and existing.is_file():
                if existing.stat().st_size == size:
                    continue
                plan.replaced_bytes += existing.stat().st_size
            plan.jobs.append(CopyJob(track, card_root / written(target) / written(spelling), size, target))
            plan.copy_bytes += size
        if name not in on_card:
            plan.new_albums.append(target)
        elif len(plan.jobs) > before:
            plan.changed_albums.append(target)
        else:
            plan.same_albums.append(target)
    return plan


def preview_add(card: Card, contents: CardContents, albums: list[Album], source: Path, plan: CopyPlan,
                replace_all: bool, tools: Tools) -> bool:
    """Show what Add will do, then ask to start. False when the user doesn't go ahead."""
    if replace_all:
        tracks = sum(len(a.tracks) for a in albums)
        say(f"[hint]Erase[/]  {plural(len(contents.albums), 'album')} · {plural(contents.tracks, 'track')} now on the card")
        say(f"[hint]Copy[/]   {plural(len(albums), 'album')} · {plural(tracks, 'track')} · {human(plan.copy_bytes)}")
        space = card.size
    else:
        parts = [plural(len(plan.new_albums), "new album")] if plan.new_albums else []
        parts += [f"{len(plan.changed_albums)} updated"] if plan.changed_albums else []
        if parts:
            say(f"[hint]Add[/]    {', '.join(parts)} · {plural(len(plan.jobs), 'track')} · {human(plan.copy_bytes)}")
            for name in plan.new_albums[:6]:
                say(f"         [accent]+[/] {esc(name)}")
            for name in plan.changed_albums[:6]:
                say(f"         [warn]~[/] {esc(name)}  [hint]changed tracks are replaced[/]")
        if plan.renames:
            say(f"[hint]Rename[/] {plural(len(plan.renames), 'album')} so the numbers run in order, no audio moved:")
            show_renames(plan.renames, Numbering.of(contents.albums), limit=6)
        if plan.same_albums:
            say(f"[hint]Keep[/]   {plural(len(plan.same_albums), 'album')} as they are")
        space = card.free + plan.replaced_bytes
    after = space - plan.copy_bytes
    say(f"[hint]Free[/]   {human(space)} {'after erasing' if replace_all else 'now'}, {human(max(after, 0))} after")
    blocker = sort_blocker(card, tools)
    if blocker:
        say(f"[hint]Then[/]   [warn]{esc(blocker)}[/]")
    else:
        password = "" if os.access(card.device, os.W_OK) else " (asks for your password)"
        say(f"[hint]Then[/]   fatsort fixes play order{password}")
    say()
    if replace_all and len(albums) < len(contents.albums):
        warn(f"The card has {plural(len(contents.albums), 'album')} now. Afterwards it will have "
             f"{len(albums)}: only what's in {esc(source.name)}.")
    if after < 0:
        warn(f"Not enough room: needs {human(plan.copy_bytes)}, has {human(space)}.")
        if not ask_confirm("Start anyway? It will stop when the card is full.", False):
            outro("Nothing was copied.", good=False)
            return False
    go = (f"Erase the card, then copy {plural(len(albums), 'album')}" if replace_all
          else f"Copy {plural(len(plan.jobs), 'track')}, then clean and sort" if plan.jobs
          else "Rename, then clean and sort")
    if ask_go(go, safe=replace_all) is BACK:  # erasing drops every album: Enter alone goes back
        outro("Nothing was copied.", good=False)
        return False
    return True


def erase_with_consent(card: Card, contents: CardContents, tools: Tools):
    """Replace everything's name gate, then the erase. The card as it is afterwards, None when stopped, or
    BACK."""
    hidden = len(contents.hidden)
    warn(f"Replace everything erases [strong]{esc(card.name)}[/]")
    say(f"{plural(len(contents.albums), 'album')} · {plural(contents.tracks, 'track')}"
        + (f" · {plural(hidden, 'hidden system item')}" if hidden else ""))
    say("The folder you copy from isn't touched. This can't be undone.")
    with doing("Erasing", card.name, red=True):
        typed = ask_text("Type the card's name to erase it:")
    if typed is BACK:
        return BACK
    if typed.strip().casefold() != card.name.casefold():
        fail("That doesn't match the card's name. Nothing was erased.")
        outro("Nothing changed.", good=False)
        return None
    RUN.card_in_use = card
    fresh = erase_card(card, tools)
    if fresh is None:
        outro("Stopped. Eject the card before you pull it out.", good=False)
    return fresh


def task_add(tools: Tools, state: dict):
    chosen = choose_card(state)
    if chosen is None:
        return BACK
    card, contents = chosen

    replace_all = False
    if contents.empty:
        say("[hint]The card is empty, so everything gets copied.[/]")
        say()
    else:
        replace_all = ask_select("Add how?", [
            option("Add albums", False, "keeps the card, copies what's new or changed", width=20),
            option("Replace everything", True, "erases the card, then copies the folder", width=20),
            back(),
        ])
        if replace_all is BACK:
            return BACK

    library = ask_library(state, "Folder with the albums to copy?")
    if library is None:
        return BACK
    source, albums = library
    with doing("Adding", f"{plural(len(albums), 'album')} from {source.name}"):
        if inside(source, card.mount) or inside(card.mount, source) or same_filesystem(source, card.mount):
            raise SafetyError("That folder is on the card itself. Pick a folder on this computer.")

        bad_names = fat_name_problems(albums)
        if bad_names:
            fail(f"{plural(len(bad_names), 'name')} can't be stored on the card:")
            listing(bad_names)
            say('[hint]Rename them without  " * : < > ? \\ |  or a trailing dot or space, shorter than '
                f"{FAT_MAX_NAME - NAME_ROOM} characters, and not differing from another only by case, "
                "then try again.[/]")
            outro("Nothing was copied.", good=False)
            return
        if not replace_all and (twice := repeated_titles([a.name for a in albums], contents.albums)):
            fail(f"Add matches albums by title, and {plural(len(twice), 'title')} "
                 f"{'is' if len(twice) == 1 else 'are'} there twice:")
            listing(twice)
            say("[hint]Give each album its own title (Arrange renames albums on the card), then try again.[/]")
            outro("Nothing was copied.", good=False)
            return

        if replace_all:  # copied as named: the folder is the whole card, e.g. a restored backup
            final, on_card, matched = {a.name: a.name for a in albums}, set(), {}
        else:
            numbering = Numbering.of(contents.albums or [a.name for a in albums])
            matched, new = match_albums(albums, contents.albums, numbering)
            placed = place_new_albums(new, contents.albums, numbering)
            if placed is BACK:
                return BACK
            final = numbering.renumber(placed)
            on_card = set(contents.albums)
        plan = plan_copy(albums, card.mount, final, on_card, matched)

        if not plan.jobs and not plan.renames:
            done("The card already has every album and track in that folder.")
            if not ask_confirm("Clean, re-sort and eject the card anyway?", False):
                outro("Nothing changed.")
                return
        elif not preview_add(card, contents, albums, source, plan, replace_all, tools):
            return

        if replace_all:
            fresh = erase_with_consent(card, contents, tools)
            if fresh is None or fresh is BACK:
                return fresh
            RUN.used.pop(card_key(card), None)  # a reformat gives the card a new ID
            card = fresh
            RUN.used[card_key(card)] = card  # so a stop from here on says it needs cleaning
            plan = plan_copy(albums, card.mount, final, set(), {})

        if IS_MAC:
            say("[hint]Keep Finder windows off the card until it ejects.[/]")
        RUN.card_in_use = card
        if plan.jobs or plan.renames:
            stamp_card(state, card, "changed")
        prepare_card(card, tools)
        if plan.renames:
            assert_card_root(card)
            with ctrl_c_shield():
                apply_renames(card.mount, plan.renames)
            done(f"Renumbered {plural(len(plan.renames), 'album')}")
        sudo = None
        if plan.jobs:
            sudo = get_admin(card, tools)  # fatsort needs it later; the file table now, so the tracks land whole
            with landing_whole(card, sudo, [job.size for job in plan.jobs]):
                copy_tracks(plan)
        save_state(state, library=str(source))
        finish_card(card, tools, state, offer_backup=bool(plan.jobs or plan.renames), sudo=sudo,
                    receipt=add_receipt(plan, replace_all))


def add_receipt(plan: CopyPlan, replace_all: bool) -> Receipt:
    """What Add changed: each new album and each album with tracks copied in, and how many renumbered."""
    receipt, tracks = Receipt(), Counter(job.album for job in plan.jobs)
    for name in plan.new_albums:
        receipt.add("+", name, plural(tracks[name], "track"))
    for name in plan.changed_albums:
        receipt.add("~", name, f"{plural(tracks[name], 'track')} copied in")
    receipt.counts += (["the card erased first"] if replace_all else []) + \
        ([f"{plural(len(plan.renames), 'album')} renumbered"] if plan.renames else [])
    return receipt



# ── Task: arrange albums ──────────────────────────────────────────────────────

def task_arrange(tools: Tools, state: dict):
    chosen = choose_card(state)
    if chosen is None:
        return BACK
    card, contents = chosen
    if not contents.albums:
        fail("The card has no albums to arrange.")
        outro("Nothing changed.", good=False)
        return

    numbering = Numbering.of(contents.albums)
    order, deleted, titles, moved = list(contents.albums), [], {}, set()
    width, last = 16, "move"
    verbs = {"move": "Move", "rename": "Rename", "delete": "Delete"}
    while True:
        renames = numbering.renames(order, titles)
        changed = bool(renames or deleted)
        actions = [
            option("Move an album", "move", "put it somewhere else; the rest renumber", width=width),
            option("Rename an album", "rename", "change its name; the number stays", width=width),
            option("Delete an album", "delete", "remove it from the card; the rest renumber", width=width),
        ]
        if changed:
            summary = ", ".join(([plural(len(deleted), "delete")] if deleted else [])
                                + ([plural(len(renames), "rename")] if renames else []))
            actions.append(option("Apply and clean", "apply", f"{summary}, then clean, sort, eject", width=width))
        elif numbering.renames(contents.albums):
            actions.append(option("Fix numbering", "apply", "close gaps and repeats, same order", width=width))
        actions.append(option("Cancel", BACK, "nothing on the card changes", width=width) if changed else back())
        action = ask_select("Arrange how?", actions, default=last)

        if action is BACK:
            if not changed:
                return BACK
            if not ask_confirm("Discard these changes?", False):
                say()
                continue
            outro("Nothing changed.")
            return
        if action == "apply":
            if confirm_arrange(card, state, numbering, order, titles, deleted, tools):
                break
            say()
            continue
        last = action
        with doing("Deleting", "an album", red=True) if action == "delete" else nullcontext():
            name = pick_album(order, f"{verbs[action]} which album?")
        if name is BACK:
            continue
        if action == "move":
            rest = [n for n in order if n != name]
            with doing("Moving", nfc(name)):
                place = pick_place(rest, "Put it where?", order.index(name))
            if place is BACK:
                continue
            order = rest[:place] + [name] + rest[place:]
            moved.add(name)
        elif action == "rename":
            with doing("Renaming", nfc(name)):
                title = ask_title(name, order, numbering, titles)
            if title is not None:
                titles[name] = title
        else:
            folder = card.mount / name
            tracks = [p for p in folder.rglob("*") if p.is_file() and not p.name.startswith(".")]
            say(f"[hint]{plural(sum(is_audio(p) for p in tracks), 'track')} · "
                f"{human(sum(p.stat().st_size for p in tracks))}. It's removed when you apply.[/]")
            order.remove(name)
            deleted.append(name)
            titles.pop(name, None)
            moved.discard(name)
        planned = [plural(len(group), word) for group, word in ((moved, "move"), (titles, "rename"), (deleted, "delete"))
                   if group]
        say(f"[hint]Planned so far: {', '.join(planned)}. Apply and clean lists every change first.[/]")
        say()

    renames = numbering.renames(order, titles)
    assert_card_root(card)
    RUN.card_in_use = card
    stamp_card(state, card, "changed")
    with ctrl_c_shield():
        for name in deleted:
            remove_album(card, name)
        apply_renames(card.mount, renames)
    parts = ([f"deleted {plural(len(deleted), 'album')}"] if deleted else []) + \
            ([f"renamed {plural(len(renames), 'album')}"] if renames else [])
    done(", ".join(parts).capitalize())
    finish_card(card, tools, state, offer_backup=not deleted,
                receipt=arrange_receipt(numbering, renames, deleted, titles, moved))


def arrange_receipt(numbering: Numbering, renames: list[tuple[str, str]], deleted: list[str],
                    titles: dict[str, str], moved: set[str]) -> Receipt:
    """What Arrange changed: each album deleted, moved or renamed, and how many others renumbered with them."""
    receipt, others = Receipt(), 0
    for gone in deleted:
        receipt.add("−", numbering.title(gone), "deleted")
    for old, new in renames:
        old_number, _, old_title = numbering.split(old)
        new_number = numbering.split(new)[0]
        if old in titles:
            receipt.add("✎", new, f"was {old_title}" + (f", {old_number}" if old in moved and old_number else ""))
        elif old in moved:
            up = not old_number or int(new_number) < int(old_number)
            receipt.add("↑" if up else "↓", new, f"was {old_number or 'unnumbered'}")
        else:
            others += 1
    if others:  # "others" only beside albums listed above it; Fix numbering lists none
        receipt.counts.append(f"{plural(others, 'other' if receipt.rows else 'album')} renumbered")
    return receipt


def confirm_arrange(card: Card, state: dict, numbering: Numbering, order: list[str], titles: dict[str, str],
                    deleted: list[str], tools: Tools) -> bool:
    """Show every change, then ask; a backup is offered before deletes. False goes back to the list."""
    renames = numbering.renames(order, titles)
    for gone in deleted:
        say(f"  [bad]delete[/] {esc(gone)}")
    show_renames(renames, numbering, limit=len(renames))
    if deleted:
        backed_up = local_date(state.get("cards", {}).get(card.uuid, {}).get("backed_up"))
        when = (f"Your last backup of this card is from {backed_up}." if backed_up
                else "No backup of this card is on record from this computer.")
        warn(f"Deleting {plural(len(deleted), 'album')} can't be undone. {when}")
    summary = ", ".join(([plural(len(deleted), "delete")] if deleted else [])
                        + ([plural(len(renames), "rename")] if renames else []))
    if ask_go(f"Apply {summary or 'the numbering'}, then clean and sort", safe=bool(deleted)) is BACK:
        return False
    if not deleted:
        return True
    # a dated backup: the next update of a kept-current one would drop what's deleted
    first = ask_confirm("Back up the card first? The albums you delete will only be in that backup.", True,
                         on_escape=BACK)
    if first is BACK:
        return False
    if first:
        say()
        if not backup_flow(tools, state, card.mount, card=card, kind="dated") and \
                not ask_confirm("Delete anyway, without a backup?", False):
            return False
        say()
    return True



# ── Task: clean the card ──────────────────────────────────────────────────────

def count_sidecars(root: Path) -> int:
    count = 0
    for _, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if not d.startswith(".")]
        count += sum(1 for f in filenames if f.startswith("._") or f in JUNK_FILES)
    return count


def task_clean(tools: Tools, state: dict):
    chosen = choose_card(state)
    if chosen is None:
        return BACK
    card, _ = chosen
    if found := hidden_clutter(card.mount):
        say(f"Removes: {esc(', '.join(found))}")
    else:
        say("[hint]No hidden files found. Cleaning still re-sorts the card and checks the play order.[/]")
    say("[hint]It also looks for tracks stored in pieces, which the radio skips, and offers to rewrite them.[/]")
    if ask_go("Clean and re-sort the card") is BACK:
        RUN.declined.add(card_key(card))
        outro("Nothing changed.")
        return
    receipt = Receipt()
    if found:
        receipt.add("−", "macOS hidden files", "removed")
    finish_card(card, tools, state, offer_backup=False, receipt=receipt)



# ── How every card task ends ──────────────────────────────────────────────────

def stamp_card(state: dict, card: Card, key: str) -> None:
    """Note now as the card's `key` time: "changed" as its albums start to change (so a stopped task still
    counts), "backed_up" once a backup of it reads back cleanly. Together they drive the menu's reminder."""
    if card.uuid:
        state.setdefault("cards", {}).setdefault(card.uuid, {"name": card.name})[key] = \
            datetime.now(UTC).isoformat(timespec="seconds")
        save_state(state)


def card_key(card: Card) -> str:
    return card.uuid or card.device


def clean_hidden(card: Card, tools: Tools, sudo: list[str] | None, *, quiet: bool = False) -> None:
    """tidy_card, then say how it went; `quiet` says only what wouldn't go."""
    leftovers = tidy_card(card, tools, sudo)
    if not leftovers:
        if not quiet:
            done("Cleaned hidden files")
        return
    warn(f"Couldn't remove {esc(', '.join(leftovers))} from the card.")
    if ".Spotlight-V100" in leftovers:
        say("[hint]Spotlight's folder needs your password or Full Disk Access for your terminal.[/]")


def finish_card(card: Card, tools: Tools, state: dict, *, offer_backup: bool, eject_now: bool = False,
                sudo: list[str] | None = None, receipt: Receipt | None = None) -> None:
    """Optional backup, then clean, mend tracks stored in pieces, sort and read the order back, and show what
    changed (the task's `receipt`, plus any track rewritten). Then eject; from the menu it asks first, since the
    card can stay mounted for the next task, and the menu then offers to finish it."""
    receipt = receipt or Receipt()
    if reason := card.problem():  # never offered for one; cleaning an e-reader's card would delete its records
        raise SafetyError(f"{card.name} can't be cleaned: {reason}.")
    RUN.card_in_use = card
    RUN.used[card_key(card)] = card
    if offer_backup:
        say()
        if (kind := ask_backup_now(card, state)) is not BACK:
            backup_flow(tools, state, card.mount, card=card, kind=kind)
            say()

    sudo = keep_admin(sudo, ask=True) if sudo is not None else get_admin(card, tools)  # Add asked already
    clean_hidden(card, tools, sudo)
    rewritten, in_pieces = mend_pieces(card, sudo, sortable=sort_blocker(card, tools) is None)
    if rewritten:  # the copies got ._ files, and macOS may have added more while they were written
        clean_hidden(card, tools, keep_admin(sudo), quiet=True)
    sudo = keep_admin(sudo, ask=True)  # fatsort finding its rights gone would leave the card unmounted and unsorted

    card = find_card(card.device, card.uuid) or card
    tree = visible_tree(card.mount)
    ordered = sort_card(card, tools, tree, sudo)
    remember_card(state, card)
    if rewritten:
        receipt.add("↻", plural(rewritten, "track"), "rewritten in one piece")
    albums = sum(name in tree and name.casefold() not in WINDOWS_DIRS for name in tree.get("", []))
    receipt.order = f"{plural(albums, 'album')} in play order" if ordered else "play order not confirmed"
    show_receipt(card, receipt)
    still = (f"{plural(in_pieces, 'track')} still in pieces, which the radio may skip. See above."
             if in_pieces else "")

    # Keep it mounted only when it can be: on Linux without udisks2, an unmounted card can't be mounted again
    if not eject_now and RUN.in_menu and (os.path.ismount(card.mount) or can_mount()) and keep_mounted():
        if os.path.ismount(card.mount) or mount_card(card):
            card = find_card(card.device, card.uuid) or card
            RUN.used[card_key(card)] = card
            RUN.active, RUN.card_in_use = (card, len(scan_card(card.mount).albums)), None
            if not ordered:
                fail("The play order isn't confirmed. See above.")
            if still:
                warn(still)
            outro("Mounted for the next task. The menu offers to clean and eject it, and asks again before you quit.",
                  good=ordered and not in_pieces)
        else:
            fail("Couldn't mount the card again.")
            outro("It's unmounted, so it's safe to pull out. Plug it in again to use it.", good=False)
        return

    if not eject_card(card):
        fail("The card didn't eject.")
        outro("Done. Eject the card before you pull it out.", good=False)
    elif not ordered:
        fail("The play order isn't confirmed. See above.")
        outro("Ejected.", good=False)
    elif still:
        warn(still)
        outro("Ejected.", good=False)
    else:
        outro("Ejected. Ready for the radio.")


def ask_backup_now(card: Card, state: dict):
    """After the card's albums changed: back it up now? Into its kept-current backup when it has one, as the
    default; otherwise a new dated one. "kept", "dated" or BACK to skip."""
    kept = find_kept(state, backup_source(card.mount, card))
    if not kept:
        return "dated" if ask_confirm("Back up the card now, into a new archive?", True) else BACK
    return ask_select("Back up the card now?", [
        option(f"Update {kept.name}", "kept", "it's rebuilt from the card as it is now", width=28),
        option("New dated backup", "dated", "a folder of its own; older backups stay as they are", width=28),
        option("Skip", BACK, width=28),
    ])


def keep_mounted() -> bool:
    eject, keep = object(), object()
    return ask_select("Then", [option("Eject", eject, "ready for the radio", width=15),
                               option("Keep it mounted", keep, "for another task; it's cleaned again before it goes back",
                                      width=15)],
                      on_escape=keep, esc_hint="") is keep


def hidden_clutter(root: Path) -> list[str]:
    """macOS's hidden files on the card: its hidden top-level entries, and how many ._ and .DS_Store files."""
    sidecars = count_sidecars(root)
    return (sorted(entry.name for entry in root.iterdir() if entry.name.startswith("."))
            + ([plural(sidecars, "._ or .DS_Store file")] if sidecars else []))


def card_problems(card: Card) -> list[str]:
    """What could trip the radio up on a mounted card, as far as can be seen without a password."""
    try:
        problems = ["hidden files macOS added"] if hidden_clutter(card.mount) else []
        if IS_MAC:  # the order is read off the mounted card only on macOS
            if out := order_problems(visible_tree(card.mount), listed_order(card.mount)):
                problems.append(f"{plural(len(out), 'folder')} out of play order")
            if card.fs in FAT_FAMILY and (pieces := quick_pieces(card.mount)):
                problems.append(f"{plural(len(pieces), 'track')} stored in pieces")
    except OSError:
        return ["it couldn't be read"]
    return problems


def cards_left_mounted() -> list[Card]:
    """The cards this run used that are still mounted, found by ID as they're mounted now. Only cards that can be
    cleaned: a locked one, read by a task that only reads, is left alone."""
    if not RUN.used:
        return []
    mounted = {card_key(card): card for card in list_cards()}
    return [mounted[key] for key in RUN.used if key in mounted and mounted[key].problem() is None]


def cards_waiting() -> list[Card]:
    """The cards to ask about before quitting. At the end of a task run straight from the command line, not the
    one just turned down: that would ask the same thing twice in a row."""
    return [card for card in cards_left_mounted() if RUN.in_menu or card_key(card) not in RUN.declined]


def before_quitting(tools: Tools, state: dict) -> bool:
    """The last step of a run that wasn't stopped: each card it used that's still mounted is checked for what could
    trip the radio up, and cleaning, re-sorting and ejecting it is offered. True when that ended the block."""
    waiting = cards_waiting()
    RUN.task = "Before quitting"
    try:
        for card in waiting:
            problems = card_problems(card)
            warn(f"{esc(card.name)} is still mounted" + (f", with {esc(', '.join(problems))}" if problems else "") + ".")
            known = bool(card.uuid) and card.uuid in (state.get("card_uuid"), RUN.confirmed and RUN.confirmed[0])
            if ask_confirm(f"Clean, re-sort and eject {card.name} before quitting?", known):
                finish_card(card, tools, state, offer_backup=False, eject_now=True)
            else:
                RUN.declined.add(card_key(card))
                outro(f"{card.name} is still mounted. Run Clean before it goes back in the radio.", good=False)
    finally:
        RUN.task = ""
    return bool(waiting)



# ── Archives ──────────────────────────────────────────────────────────────────

class HashingReader:
    """Wraps a file so tarfile's reads also feed the checksum and the progress bar: one read per file."""

    def __init__(self, source, on_bytes):
        self.source = source
        self.sha = hashlib.sha256()
        self.on_bytes = on_bytes

    def read(self, size: int = -1) -> bytes:
        data = self.source.read(size)
        self.sha.update(data)
        self.on_bytes(len(data))
        return data


class CountingReader:
    """Counts compressed bytes read, so progress follows the archive file itself."""

    def __init__(self, source, on_bytes):
        self.source = source
        self.on_bytes = on_bytes

    def read(self, size: int = -1) -> bytes:
        data = self.source.read(size)
        self.on_bytes(len(data))
        return data

    def readinto(self, buffer) -> int:
        count = self.source.readinto(buffer) or 0
        self.on_bytes(count)
        return count

    def readable(self) -> bool:
        return True

    def close(self) -> None:
        self.source.close()

    @property
    def closed(self) -> bool:
        return self.source.closed


@contextmanager
def open_archive(archive: Path, on_bytes=lambda n: None, *, to_the_end: bool = True):
    """Stream any of our archive types: new .tar.zst, or the .tar.xz / .bz2 / .gz older backups use.
    Reading on to the very end makes every format check its trailing checksum (gzip's comes after the tar)."""
    name = archive.name
    if not name.endswith(ARCHIVE_SUFFIXES):
        raise ValueError(f"not a backup archive: {name}")
    with ExitStack() as stack:
        counted = CountingReader(stack.enter_context(open(archive, "rb")), on_bytes)
        if name.endswith(".tar.zst"):
            stream = zstd.ZstdFile(counted, "r")
        elif name.endswith(".tar.xz"):
            stream = lzma.LZMAFile(counted, "r")
        elif name.endswith(".tar.bz2"):
            stream = bz2.BZ2File(counted, "r")
        else:
            stream = gzip.GzipFile(fileobj=counted, mode="rb")
        stack.enter_context(stream)
        yield stack.enter_context(tarfile.open(fileobj=stream, mode="r|"))
        if to_the_end:
            while stream.read(1 << 20):
                pass


READ_ERRORS = (tarfile.TarError, EOFError, OSError, ValueError, zstd.ZstdError, lzma.LZMAError)


def apple_double(name: str) -> bool:
    """macOS tar stores extended attributes as ._name entries; they're metadata, not library files."""
    return Path(name).name.startswith("._")


def unlistable(name: str) -> bool:
    """A line-based checksum file can't hold a name with a line break: any break splitlines() splits on,
    since read_manifest reads it with that (form feeds and the like, as well as newlines)."""
    return name.splitlines() != [name]


def durable(handle) -> None:
    """Push a file's data all the way to the drive before we call it done."""
    handle.flush()
    os.fsync(handle.fileno())
    if IS_MAC:
        try:
            fcntl.fcntl(handle.fileno(), fcntl.F_FULLFSYNC)  # fsync alone stops at the drive's cache on macOS
        except OSError:
            pass


def filesystem_of(path: Path) -> str:
    """The filesystem a path is on, e.g. apfs, msdos, exfat or vfat. diskutil only answers for a volume's
    own top folder, so walk up to it first."""
    mount = Path(os.path.realpath(nearest_existing(path) or path))
    while not os.path.ismount(mount):
        mount = mount.parent
    return _filesystem_at(str(mount))


@functools.cache  # asked on every keystroke in a path field
def _filesystem_at(mount: str) -> str:
    if IS_MAC:
        return (diskutil_info(mount).get("FilesystemType") or "").lower()
    return _mount_types().get(mount, "").lower()


def partial_copy(name: str) -> bool:
    """A track Add was copying when it was stopped (.Name.flac.part): half a file, never worth keeping."""
    return name.startswith(".") and name.endswith(".part")


def library_entries(root: Path) -> tuple[list[Path], list[Path], int, list[str]]:
    """Everything worth keeping under the library: folders and files, minus OS clutter. Linked folders
    and files are followed, as Add follows them. The last item lists what can't be read."""
    entries, files, total, problems = [], [], 0, []

    def note(error: OSError):
        problems.append(f"{_relative(error.filename, root)}: {error.strerror or 'unreadable'}")

    for dirpath, dirnames, filenames in os.walk(root, followlinks=True, onerror=note):
        here = Path(dirpath)
        # Only a link back into a folder it's inside is skipped, a loop. A linked album is kept even when the album
        # it points at is there too, as Add copies both.
        inside = {os.path.realpath(root / parent) for parent in here.relative_to(root).parents}
        if here != root and os.path.realpath(here) in inside:
            dirnames[:] = []
            continue
        if here != root:
            entries.append(here)
        top = here == root
        dirnames[:] = sorted((d for d in dirnames if d not in JUNK_DIRS and not (top and d.startswith("."))),
                             key=natural_key)
        for name in sorted(filenames, key=natural_key):
            if name in JUNK_FILES or name.startswith("._") or (top and name.startswith(".")) or partial_copy(name):
                continue
            path = here / name
            try:
                size = path.stat().st_size
            except OSError as error:
                problems.append(f"{_relative(path, root)}: {error.strerror or 'broken link'}")
                continue
            if not path.is_file():
                problems.append(f"{_relative(path, root)}: not a regular file")
            elif not os.access(path, os.R_OK):
                problems.append(f"{_relative(path, root)}: can't be read")
            else:
                entries.append(path)
                files.append(path)
                total += size
    return entries, files, total, problems


def _relative(path, root: Path) -> str:
    try:
        return str(Path(path).relative_to(root))
    except ValueError:
        return str(path)


def write_archive(library: Path, entries: list[Path], archive: Path, manifest: Path, on_bytes) -> int:
    """tar + zstd and the SHA-256 manifest in one pass. Writes .partial files, pushes them to the drive,
    and renames them only when complete, so a stopped backup never looks finished. Returns how many
    names the manifest had to skip."""
    params = zstd.CompressionParameter
    options = {params.compression_level: ZSTD_LEVEL, params.checksum_flag: 1}
    most_workers = params.nb_workers.bounds()[1]
    if most_workers > 0:
        options[params.nb_workers] = min(os.cpu_count() or 1, most_workers)

    archive_part = sidecar(archive, ".partial")
    manifest_part = sidecar(manifest, ".partial")
    skipped = 0
    try:
        with open(archive_part, "wb") as raw, open(manifest_part, "w", encoding="utf-8", errors="surrogateescape", newline="\n") as sums:
            if IS_MAC:
                fcntl.fcntl(raw.fileno(), fcntl.F_NOCACHE, 1)  # not kept in RAM: the read-back has to read the drive
            # dereference: a linked album or track is stored as the audio itself, the way Add copies it
            with (zstd.ZstdFile(raw, "w", options=options) as compressed,
                  tarfile.open(fileobj=compressed, mode="w|", format=tarfile.PAX_FORMAT, dereference=True) as tar):
                for path in entries:
                    name = f"{library.name}/{path.relative_to(library).as_posix()}"
                    info = tar.gettarinfo(str(path), arcname=name)
                    if not info.isreg():
                        tar.addfile(info)
                        continue
                    with open(path, "rb") as source:
                        reader = HashingReader(source, on_bytes)
                        tar.addfile(info, reader)
                    if unlistable(name):
                        skipped += 1
                    else:
                        sums.write(f"{reader.sha.hexdigest()}  {name}\n")
            durable(raw)
            durable(sums)
            if hasattr(os, "posix_fadvise"):  # Linux: drop the cached copy for the same reason
                os.posix_fadvise(raw.fileno(), 0, 0, os.POSIX_FADV_DONTNEED)
        os.replace(archive_part, archive)
        os.replace(manifest_part, manifest)
    except BaseException:
        archive_part.unlink(missing_ok=True)
        manifest_part.unlink(missing_ok=True)
        raise
    return skipped


def read_manifest(manifest: Path) -> tuple[dict[str, str], int]:
    """Reads `sha256sum` / `shasum -a 256` format, ours and older backups'. Also counts lines that
    aren't checksums, so a damaged list can't pass quietly."""
    wanted, unreadable = {}, 0
    for line in manifest.read_text(encoding="utf-8", errors="surrogateescape").splitlines():
        if not line.strip():
            continue
        match = re.match(r"^\\?([0-9a-fA-F]{64}) [ *](.+)$", line)
        if match:
            wanted[match.group(2)] = match.group(1).lower()
        else:
            unreadable += 1
    return wanted, unreadable


@dataclass
class Checked:
    ok: int = 0
    files: int = 0
    bad: list[str] = field(default_factory=list)
    missing: list[str] = field(default_factory=list)
    unlisted: list[str] = field(default_factory=list)   # present, but the checksum list doesn't know them
    unreadable_lines: int = 0                            # lines in the checksum list that aren't checksums

    @property
    def passed(self) -> bool:
        return not (self.bad or self.missing or self.unlisted or self.unreadable_lines)


def _sha256(source, on_bytes) -> str:
    sha = hashlib.sha256()
    while chunk := source.read(1 << 20):
        sha.update(chunk)
        on_bytes(len(chunk))
    return sha.hexdigest()


def verify_archive(archive: Path, manifest: Path | None, on_bytes) -> Checked:
    """Read every file inside the archive and compare it with the manifest, without unpacking."""
    checked, wanted = Checked(), {}
    if manifest:
        listed, checked.unreadable_lines = read_manifest(manifest)
        wanted = {nfc(k): v for k, v in listed.items()}
    digests = {}
    with open_archive(archive, on_bytes) as tar:
        for member in tar:
            if apple_double(member.name):
                continue
            key = nfc(member.name)
            if member.isfile():
                digest = digests[key] = _sha256(tar.extractfile(member), lambda n: None)
            elif member.islnk():
                digest = digests.get(nfc(member.linkname))  # a hard link's data is its target's
            else:
                continue
            checked.files += 1
            if not manifest:
                continue
            if key not in wanted:
                if not unlistable(member.name):
                    checked.unlisted.append(member.name)
            elif digest == wanted.pop(key):
                checked.ok += 1
            else:
                checked.bad.append(member.name)
    checked.missing = sorted(wanted)
    return checked


def extract_archive(archive: Path, dest: Path, on_bytes) -> list[str]:
    """Unpack with Python's "data" filter: nothing lands outside `dest`, no devices, no odd permissions.
    Skips macOS ._ metadata, and links that would point outside `dest` (returned, to report)."""
    skipped = []
    with open_archive(archive, on_bytes) as tar:
        for member in tar:
            if apple_double(member.name):
                continue
            try:
                safe = tarfile.data_filter(member, str(dest))  # leading "/" stripped, link target checked
            except tarfile.FilterError:
                if member.issym() or member.islnk():
                    skipped.append(member.name)
                    continue
                raise
            if member.islnk():
                try:
                    tar.extract(member, path=dest, filter="data")
                except (OSError, tarfile.TarError):
                    link = dest / safe.name  # drives without hard links (FAT, exFAT) get a copy instead
                    link.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(dest / safe.linkname, link)
                continue
            tar.extract(member, path=dest, filter="data")
    return skipped


def unpack_to_staging(archive: Path, dest: Path, on_bytes) -> tuple[Path, list[str]]:
    """Unpack into a hidden folder inside `dest`. Nothing already there is touched until every file checks out."""
    staging = dest / f".tecsun-restore-{os.getpid()}"
    staging.mkdir(parents=True)
    try:
        return staging, extract_archive(archive, staging, on_bytes)
    except BaseException:
        shutil.rmtree(staging, ignore_errors=True)
        raise


def move_into_place(staging: Path, dest: Path) -> list[str]:
    """Move checked files from staging into `dest`, replacing same-named files. Returns what couldn't move."""
    stuck = []

    def replace(src: Path, dst: Path):
        try:
            os.replace(src, dst)
        except OSError:  # e.g. a locked file there: the rest still move, and this one's copy stays in staging
            stuck.append(str(dst))

    def merge(src: Path, dst: Path):
        if not dst.exists() and not dst.is_symlink():
            replace(src, dst)
        elif src.is_dir() and not src.is_symlink() and dst.is_dir() and not dst.is_symlink():
            for child in list(src.iterdir()):
                merge(child, dst / child.name)
        elif not src.is_dir() and not dst.is_dir():
            replace(src, dst)
        else:
            stuck.append(str(dst))

    for child in list(staging.iterdir()):
        merge(child, dest / child.name)
    if not stuck:
        shutil.rmtree(staging, ignore_errors=True)
    return stuck


def set_aside(staging: Path, dest: Path, top: str) -> Path:
    """Keep files that failed their check in a visible folder of their own, beside the restore."""
    stamp = datetime.now().astimezone().date().isoformat()
    folder, number = dest / f"{top} (unverified {stamp})", 2
    while folder.exists():
        folder, number = dest / f"{top} (unverified {stamp} {number})", number + 1
    os.replace(staging, folder)
    return folder


def verify_files(root: Path, manifest: Path, on_bytes) -> Checked:
    """Compare the files under `root` with the manifest: changed, missing and extra files all count."""
    listed, unreadable = read_manifest(manifest)
    checked = Checked(unreadable_lines=unreadable)
    wanted = {nfc(k): v for k, v in listed.items()}
    for path in sorted(p for p in root.rglob("*") if p.is_file() and not p.is_symlink()):
        name = path.relative_to(root).as_posix()
        key = nfc(name)
        checked.files += 1
        if key not in wanted:
            if not unlistable(name):
                checked.unlisted.append(name)
            continue
        with open(path, "rb") as source:
            same = _sha256(source, on_bytes) == wanted.pop(key)
        if same:
            checked.ok += 1
        else:
            checked.bad.append(name)
    checked.missing = sorted(wanted)
    return checked


def report_checked(checked: Checked, what: str = "file") -> bool:
    if checked.passed:
        done(f"All {plural(checked.ok, what)} match their checksums")
        return True
    parts = [f"{len(checked.bad)} changed", f"{len(checked.missing)} missing"]
    if checked.unlisted:
        parts.append(f"{len(checked.unlisted)} not in the checksum list")
    if checked.unreadable_lines:
        parts.append(f"{checked.unreadable_lines} damaged checksum lines")
    fail(", ".join(parts) + f", {checked.ok:,} fine")
    listing([f"changed  {n}" for n in checked.bad] + [f"missing  {n}" for n in checked.missing]
            + [f"not listed  {n}" for n in checked.unlisted])
    return False


def archive_top_folder(archive: Path, manifest: Path) -> str:
    """The library folder's name inside the archive. macOS ._ metadata entries don't count."""
    if manifest.is_file():
        for name in read_manifest(manifest)[0]:
            return name.split("/", 1)[0]
    try:
        with open_archive(archive, to_the_end=False) as tar:
            for member in tar:
                if not apple_double(member.name):
                    return member.name.split("/", 1)[0]
    except READ_ERRORS:
        pass
    return archive.name.split(".tar.")[0]


PAR2_PROGRESS = re.compile(rb"(Loading|Scanning|Constructing|Processing|Verifying|Repairing|Computing|Opening)"
                           rb"[^:\r\n]*:\s*(\d+(?:\.\d+)?)%")


def run_par2(args: list[str], cwd: Path, label: str) -> tuple[int, str]:
    """par2 with its own percentage driving the bar. It runs in a session of its own, so Ctrl-C reaches
    only us; we stop par2 and the caller cleans up after it."""
    try:
        process = subprocess.Popen(["par2", *args], cwd=cwd, stdin=subprocess.DEVNULL,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT, start_new_session=True)
    except FileNotFoundError:  # removed since the run started: the callers say so, as for any par2 failure
        return 127, "par2 isn't installed"
    output = bytearray()

    def drain():
        while chunk := process.stdout.read1(4096):
            output.extend(chunk)

    reader = threading.Thread(target=drain, daemon=True)
    reader.start()
    try:
        with progress_bar() as bar:
            task = bar.add_task("", total=100, detail=label, note="")
            while process.poll() is None:
                found = PAR2_PROGRESS.findall(bytes(output[-4096:]))
                if found:
                    phase, percent = found[-1]
                    bar.update(task, completed=min(float(percent), 99.9), note=phase.decode().lower())
                time.sleep(0.2)
    except BaseException:
        process.terminate()
        try:
            process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            process.kill()
            process.wait()
        raise
    reader.join(timeout=2)
    return process.returncode, output.decode(errors="replace")


def remove_parity(archive: Path) -> None:
    """Delete an incomplete repair-data set, so it can't later pass for damage."""
    for path in archive.parent.glob(glob.escape(archive.name) + "*.par2"):
        path.unlink(missing_ok=True)


def check_parity(archive: Path, tools: Tools, *, repair: bool) -> str:
    """'ok', 'repaired', 'damaged' (fixable, repair not asked for), 'failed' or 'skipped'.
    Only real damage counts against the backup. Unusable repair data is skipped: the checksums still decide."""
    parity = sidecar(archive, ".par2")
    if not parity.is_file():
        say("[hint]No repair data next to this backup.[/]")
        return "skipped"
    if not tools.par2:
        warn(f"par2 isn't installed, so the repair data can't be used ({install_hint('par2')}).")
        return "skipped"
    code, output = run_par2(["verify", "--", parity.name], archive.parent, "checking repair data")
    if code == 0:
        done("Repair data says the backup is intact")
        return "ok"
    if code == 127:
        warn(f"par2 isn't installed any more, so the repair data can't be used ({install_hint('par2')}).")
        return "skipped"
    if re.search(r'Target: ".*" - missing', output):
        warn("The repair data is for a file with another name, so it was skipped.")
        return "skipped"
    if code not in (1, 2):
        warn(f"The repair data itself is unreadable (par2 code {code}), so it was skipped. "
             "The checksums still check every file.")
        return "skipped"
    if code == 2:
        fail("The backup is damaged beyond what its repair data can fix.")
        return "failed"
    if not repair:
        warn("Repair data found damage it can fix. Restore repairs it before unpacking.")
        return "damaged"
    warn("Repair data found damage. Repairing…")
    kept_aside = glob.escape(archive.name) + ".[0-9]*"  # par2 keeps the damaged original as <name>.1
    before = set(archive.parent.glob(kept_aside))
    code, _ = run_par2(["repair", "--", parity.name], archive.parent, "repairing")
    if code == 0:
        for leftover in set(archive.parent.glob(kept_aside)) - before:  # par2 checked the repaired file already
            leftover.unlink(missing_ok=True)
        done("Repaired from the repair data")
        return "repaired"
    fail("Couldn't repair the backup.")
    return "failed"


def find_archives(state: dict) -> list[Path]:
    """The 8 newest backups: in the current folder, the backups folder in use and the default one, beside the
    last one used, and on plugged-in drives."""
    roots = [(Path.cwd(), 1), (backups_from(state), 2), (DEFAULT_BACKUPS, 2)]
    if state.get("last_archive"):
        roots.append((Path(state["last_archive"]).parent, 1))
    roots += [(card.mount, 2) for card in list_cards()]

    found = {}

    def look(folder: Path, depth: int):
        try:
            entries = list(os.scandir(folder))
        except OSError:
            return
        for entry in entries:
            if entry.name.startswith("."):
                continue
            if entry.is_file() and entry.name.endswith(ARCHIVE_SUFFIXES):
                path = Path(entry.path)
                found[path.resolve()] = path
            elif depth > 1 and entry.is_dir(follow_symlinks=False):
                look(Path(entry.path), depth - 1)

    for root, depth in roots:
        look(root, depth)
    return sorted(found.values(), key=lambda p: p.stat().st_mtime, reverse=True)[:8]


def pick_archive(state: dict, message: str) -> Path | None:
    archives = find_archives(state)
    width = max((len(a.name) for a in archives), default=0)
    choices = []
    for archive in archives:
        stamp = time.strftime("%Y-%m-%d", time.localtime(archive.stat().st_mtime))
        hint = f"{tilde(archive.parent)} · {human(archive.stat().st_size)} · {stamp}"
        choices.append(option(archive.name, archive, hint, width=width))
    choices += [divider()] if choices else []
    choices += [action_choice("Other file…", "other", "→", hint="type a path or drag the file in"), back()]
    while True:
        picked = ask_select(message, choices)
        if picked is BACK:
            return None
        if picked != "other":
            return picked
        places = [(tilde(p.parent) + "/", "") for p in archives[:3]]
        typed = ask_path("Which backup file?", "", places, must_exist=True, archive=True)
        if typed is not BACK:
            return typed


def backups_from(state: dict) -> Path:
    """The folder last typed at "Save the backup where?", or the default beside the script."""
    return Path(state["backup_dir"]) if state.get("backup_dir") else DEFAULT_BACKUPS


def remember_backups(state: dict, folder: Path) -> None:
    """A typed backups folder is remembered, and said to be; the default isn't, so it stays the default."""
    before = backups_from(state)
    if inside(folder, DEFAULT_BACKUPS) and inside(DEFAULT_BACKUPS, folder):
        state.pop("backup_dir", None)
        saved = save_state(state)
    else:
        saved = save_state(state, backup_dir=str(folder))
    if before.resolve() == folder.resolve():
        return
    if saved:
        done(f"Backups go to {esc(tilde(folder))} from now on.")
        with suppress(OSError):
            if before.is_dir() and any(before.iterdir()):
                say(f"[hint]Backups already saved stay in {esc(tilde(before))}.[/]")
    else:
        warn(f"{esc(tilde(STATE_FILE))} couldn't be saved, so the next backup starts in {esc(tilde(before))} again.")


def backups_note(state: dict) -> str:
    """The backups folder in use, said for help: the default, or picked, and whether it's there."""
    folder = backups_from(state)
    if folder == DEFAULT_BACKUPS:
        return "backups; the default, beside the script"
    if folder.is_dir():
        return "backups; the folder you picked"
    drive = unplugged(folder)
    return "backups; the folder you picked, but " + (f"{drive} isn't plugged in" if drive else "it isn't there")


def backup_places(state: dict, source: Path | None = None) -> list[tuple[str, str]]:
    """Suggestions for "Save the backup where?": the folder in use, the default, other drives (not the card being
    backed up), Desktop and Documents."""
    folder = backups_from(state)
    places = [(tilde(folder) + "/", "in use")]
    if folder != DEFAULT_BACKUPS:
        places.append((tilde(DEFAULT_BACKUPS) + "/", "the default, beside the script"))
    places += [(str(c.mount) + "/", f"{c.kind} · {human(c.free)} free") for c in list_cards()
               if not (source and inside(source, c.mount))]
    places += [(tilde(p) + "/", "") for p in (HOME / "Desktop", HOME / "Documents") if p.is_dir()]
    seen, unique = set(), []
    for path, label in places:
        if path not in seen:
            seen.add(path)
            unique.append((path, label))
    return unique


def dated_folder(parent: Path) -> Path:
    stamp = datetime.now().astimezone().date().isoformat()  # local date: it's a folder name people read
    folder, number = parent / stamp, 2
    while folder.exists():
        folder, number = parent / f"{stamp}-{number}", number + 1
    return folder


def free_space(path: Path) -> int:
    anchor = nearest_existing(path) or path
    try:
        return shutil.disk_usage(anchor).free
    except OSError:
        return 0



# ── Audio checks ──────────────────────────────────────────────────────────────

def test_audio_file(path: Path, tools: Tools) -> bool | None:
    """True plays cleanly, False is damaged, None means it couldn't be judged: no tool here decodes that type, or
    the decode ran out of time. The limit grows with the file (half a megabyte a second at worst, as from a slow
    reader shared by eight decodes), so a long recording isn't called damaged for being long."""
    limit = max(300, path.stat().st_size / 500_000)
    if path.suffix.lower() == ".flac" and tools.flac:
        result = run(["flac", "-t", "-s", "--", str(path)], timeout=limit, detail=True)
        return None if result.returncode == 124 else result.returncode == 0
    if tools.ffmpeg:
        # ffmpeg exits 0 even on damaged files, so judge it by whether it complained.
        result = run(["ffmpeg", "-nostdin", "-v", "error", "-i", str(path), "-f", "null", "-"], timeout=limit,
                     detail=True)
        return None if result.returncode == 124 else result.returncode == 0 and not result.stderr.strip()
    return None


@dataclass
class AudioReport:
    ok: int = 0
    failed: list[Path] = field(default_factory=list)
    untested: int = 0


def check_audio(files: list[Path], tools: Tools) -> AudioReport:
    audio = [f for f in files if is_audio(f)]
    total = sum(f.stat().st_size for f in audio)
    report = AudioReport()
    pool = ThreadPoolExecutor(max_workers=min(8, os.cpu_count() or 2))
    try:
        with progress_bar() as bar:
            task = bar.add_task("", total=max(total, 1), detail="", note="decoding every track")
            jobs = {pool.submit(test_audio_file, f, tools): f for f in audio}
            for number, job in enumerate(as_completed(jobs), 1):
                path = jobs[job]
                result = job.result()
                if result is True:
                    report.ok += 1
                elif result is False:
                    report.failed.append(path)
                else:
                    report.untested += 1
                bar.update(task, advance=path.stat().st_size, detail=f"{number}/{len(audio)} tracks")
    finally:
        pool.shutdown(wait=True, cancel_futures=True)  # on Ctrl-C, queued tracks are dropped, not decoded
    report.failed.sort(key=lambda p: natural_key(str(p)))
    return report


def show_audio_report(report: AudioReport, root: Path, tools: Tools) -> None:
    untested = f", {report.untested:,} untested (no tool for that type, or too slow to finish)" if report.untested else ""
    if report.failed:
        fail(f"{plural(len(report.failed), 'track')} failed: these may skip or glitch")
        listing([str(p.relative_to(root)) for p in report.failed])
        say(f"[ok]{report.ok:,} passed[/]{untested}")
    else:
        done(f"All {plural(report.ok, 'track')} decode cleanly{untested}")
    if report.untested and not tools.ffmpeg:  # said here, when it matters, not at every start
        say(f"[hint]Tracks other than FLAC need ffmpeg to be checked ({install_hint('ffmpeg')}).[/]")



# ── Task: back up ─────────────────────────────────────────────────────────────

def pick_card_or_folder(state: dict, question: str, folder_hint: str):
    """For a task that only reads a card: a usable card, "folder", or BACK. When there's no card to pick it says
    so, with the folder and Rescan to choose from, rather than going straight to a folder."""
    while True:
        cards = rank_cards(list_cards(), state.get("card_uuid"))
        usable = [c for c in cards if c.problem(changes=False) is None]
        if not cards:
            warn("No SD card found. Insert the card, then pick Rescan, or pick a folder.")
        elif not usable:
            warn("None of these cards can be used; the reason is beside each.")
        width = max([len("A folder"), *(len(c.name) for c in cards)])
        picked = ask_select(question, [
            *[option(c.name, c, f"the card · {human(c.size)} {c.kind}", width=width, disabled=c.problem(changes=False))
              for c in cards],
            *([divider()] if cards else []),
            action_choice("A folder", "folder", "→", hint=folder_hint),
            action_choice("Rescan", "rescan", "↻"),
            back(),
        ], default=usable[0] if usable else "folder")
        if picked != "rescan":
            if isinstance(picked, Card):
                RUN.used[card_key(picked)] = picked
            return picked


def offer_finish(card: Card, tools: Tools, state: dict) -> None:
    """After a task read a card in place (macOS leaves hidden files on it): clean, re-sort and eject it now,
    or end by saying it still needs that. Yes is the default only for the card used last. A card that can't be
    changed (locked, or with no volume ID) is never offered it."""
    say()
    if not card.writable:  # macOS couldn't add anything to it
        outro("Done. The card is locked, so nothing was added to it. Eject it before you pull it out.")
        return
    if reason := card.problem():
        outro(f"Done. It can't be cleaned here: {esc(reason)}. Eject it before you pull it out.", good=False)
        return
    if ask_confirm(f"Clean, re-sort and eject {card.name} now?", card.uuid == state.get("card_uuid")):
        finish_card(card, tools, state, offer_backup=False)
    else:
        RUN.declined.add(card_key(card))
        outro("The card is still mounted. Run Clean before it goes back in the radio.", good=False)


def task_backup(tools: Tools, state: dict):
    picked = pick_card_or_folder(state, "Back up what?", "a library folder on this computer")
    if picked is BACK:
        return BACK
    if picked == "folder":
        library = ask_library(state, "Back up which folder?")
        if library is None:
            return BACK
        good = backup_flow(tools, state, library[0])
        outro("Done." if good else "No backup was made.", good=good)
        return
    backup_flow(tools, state, picked.mount, card=picked)
    offer_finish(picked, tools, state)


def backup_flow(tools: Tools, state: dict, library: Path, *, card: Card | None = None, kind: str | None = None) -> bool:
    """Back up a folder or a card, into a new dated folder ("dated") or its kept-current backup ("kept"); asked
    when `kind` is None. True when a backup was written and read back cleanly. It never ends the run, so a card
    task can carry on afterwards."""
    with doing("Backing up", card.name if card else library.name):
        entries, files, total, problems = library_entries(library)
        if problems:
            fail(f"{plural(len(problems), 'item')} can't be read, so the backup would be incomplete:")
            listing(problems)
            say("[hint]Fix their permissions or move them out, then back up again.[/]")
            return False
        say(f"[hint]{plural(len(files), 'file')} · {human(total)}[/]")
        say()

        def destination_problem(path: Path) -> str | None:
            if inside(path, library):
                return "That's inside the library. Pick a folder outside it."
            if total * 1.01 > FAT_MAX_FILE and filesystem_of(path) in FOUR_GB_FILESYSTEMS:
                return f"That drive is FAT, which can't hold a file over 4 GB, and this backup is about {human(total)}."
            return None

        name = card.name if card else library.name
        source = backup_source(library, card)
        kept = find_kept(state, source)
        if kind is None:
            kind = ask_backup_kind(kept, name, can_keep=not card or bool(card.uuid))
            if kind is BACK:
                say("[hint]No backup made.[/]")
                return False

        chosen = None  # a backups folder typed below
        if kind == "kept" and kept is None:
            parent = ask_path("Save the backup where?", tilde(backups_from(state)), backup_places(state, library),
                              must_exist=False, check=destination_problem)
            if parent is BACK:
                say("[hint]No backup made.[/]")
                return False
            chosen = parent
            kept = parent / f"{name}{KEPT}"
            saved = read_source(kept)
            if saved and not same_source(saved, source):
                warn(f"{esc(tilde(kept))} is already the kept-current backup of {esc(str(saved.get('name') or 'another'))}.")
                if not ask_confirm("Replace it with this one?", False):
                    return False
            elif not saved and kept.is_dir() and any(entry.name != ".new" for entry in kept.iterdir()):
                fail(f"{esc(tilde(kept))} is already there, and isn't a kept-current backup. Nothing was written.")
                return False
        if kind == "kept":
            if problem := destination_problem(kept):  # a card that grew past 4 GB since it was started on FAT
                fail(f"Can't back up into {esc(tilde(kept))}: {esc(problem)}")
                say("[hint]Pick New dated backup and a drive that isn't FAT, or move the kept-current backup to one.[/]")
                return False
            folder, staging = kept, kept / ".new"  # built beside the old one, under its final names, then moved in
            settle_kept(folder)
        else:
            parent = ask_path("Save the backup where?", tilde(backups_from(state)), backup_places(state, library),
                              must_exist=False, check=destination_problem)
            if parent is BACK:
                say("[hint]No backup made.[/]")
                return False
            chosen = parent
            folder = staging = dated_folder(parent)

        archive = staging / f"{library.name}.tar.zst"
        manifest = sidecar(archive, ".sha256")
        parity = sidecar(archive, ".par2")
        with_parity = tools.par2 and PARITY_PERCENT > 0
        old = next((p for p in sorted(folder.glob("*.tar.zst"))), None) if kind == "kept" and folder.is_dir() else None
        before = backed_up_names(sidecar(old, ".sha256")) if old else {}

        changes = None
        if old:
            updated = local_date((read_source(folder) or {}).get("updated"))
            say(f"Updates  [strong]{esc(tilde(folder))}/[/]" + (f"  [hint]last updated {updated}[/]" if updated else ""))
            if before is None:
                warn("Its checksum list is missing or damaged, so what this update would drop can't be told.")
            else:
                changes = compare_with_backup(list(before), [path.relative_to(library).as_posix() for path in files])
                show_backup_changes(changes)
        else:
            holds = "the archive, its checksums" + (" and repair data" if with_parity else "")
            say(f"Creates  [strong]{esc(tilde(folder))}/[/]  [hint]{holds}"
                + ("; kept current, so later backups update it" if kind == "kept" else "") + "[/]")
        if not with_parity:
            say(f"  [hint]No repair data: par2 isn't installed ({install_hint('par2')}).[/]")
        needed = int(total * (1 + (PARITY_PERCENT / 100 if with_parity else 0)))
        room = free_space(folder)
        say(f"[hint]Needs about {human(needed)}, {human(room)} free there"
            + (", while the old copy stays until the new one checks out" if old else "") + "[/]")
        say()
        if needed > room and not ask_confirm("Not enough room there. Start anyway?", False):
            return False
        removes = bool(old) and (changes is None or changes.removes)  # not known counts as dropping
        if ask_go(f"Update {folder.name}" if old else f"Back up {name}", safe=removes) is BACK:
            return False

        if tools.flac or tools.ffmpeg:
            say("[hint]Checking the audio first, so a damaged track isn't archived unnoticed.[/]")
            failed_before = RUN.failed, RUN.task_failed
            report = check_audio(files, tools)
            show_audio_report(report, library, tools)
            if report.failed and not ask_confirm("Back up anyway? Damaged tracks are stored as they are.", False):
                say("[hint]Fix or remove the tracks above, then back up again.[/]")
                return False
            RUN.failed, RUN.task_failed = failed_before  # damage seen and accepted: the backup is what counts
        else:
            say(f"[hint]Audio check skipped: needs flac or ffmpeg ({install_hint('flac', 'ffmpeg')}).[/]")

        if chosen:  # remembered only once the backup goes ahead
            remember_backups(state, chosen)
        staging.mkdir(parents=True)
        try:
            with progress_bar() as bar:
                task = bar.add_task("", total=max(total, 1), detail="packing", note=f"zstd level {ZSTD_LEVEL}")
                skipped = write_archive(library, entries, archive, manifest, lambda n: bar.advance(task, n))
        except BaseException as error:
            if kind == "kept":
                shutil.rmtree(staging, ignore_errors=True)
                with suppress(OSError):
                    folder.rmdir()  # only when it was new, so empty
            else:
                with suppress(OSError):
                    shutil.rmtree(folder)  # a dated folder holds only this backup's half-written files
            if not isinstance(error, OSError):
                raise
            fail(f"The backup couldn't be written: {esc(error.strerror or str(error))}"
                 + (f" ({esc(tilde(error.filename))})" if error.filename else ""))
            say("[hint]" + ("The kept-current backup stays as it was. " if kind == "kept" else "")
                + "Free up room, or back up to another drive.[/]")
            return False
        done(f"Packed {plural(len(files), 'file')} into {esc(archive.name)} ({human(archive.stat().st_size)})")
        if skipped:
            warn(f"{plural(skipped, 'file')} with a line break in the name can't be in the checksum list. They're in the archive.")

        try:
            with progress_bar() as bar:
                task = bar.add_task("", total=archive.stat().st_size, detail="reading it back", note="")
                checked = verify_archive(archive, manifest, lambda n: bar.advance(task, n))
        except READ_ERRORS as error:
            fail(f"The backup didn't read back: {esc(str(error))}")
            if kind == "kept":
                shutil.rmtree(staging, ignore_errors=True)
                warn("The kept-current backup stays as it was. Try another drive.")
            else:
                warn(f"Delete {esc(tilde(folder))} and back up to another drive.")
            return False
        if not report_checked(checked):
            if kind == "kept":
                shutil.rmtree(staging, ignore_errors=True)
                warn("The new copy didn't read back cleanly, so the kept-current backup stays as it was. "
                     "Try another drive.")
            else:
                warn(f"Delete {esc(tilde(folder))}: it doesn't match what was packed. Back up to another drive.")
            return False

        if with_parity:  # only for a backup that read back cleanly: repair data for a bad one would vouch for it
            try:
                code, _ = run_par2(["create", f"-r{PARITY_PERCENT}", "--", parity.name, archive.name, manifest.name],
                                   staging, "building repair data")
            except BaseException:
                remove_parity(archive)
                raise
            if code == 0:
                done(f"Repair data written, {PARITY_PERCENT}%")
            else:
                remove_parity(archive)
                warn("par2 couldn't build repair data, so none was kept. The backup and checksums are fine without it.")

        if kind == "kept":
            if not replace_kept(folder, staging, before, source | {"name": name}):
                return False
            archive = folder / archive.name

        os.sync()
        save_state(state, last_archive=str(archive))
        if card is None:
            save_state(state, library=str(library))
        else:
            stamp_card(state, card, "backed_up")
        done(f"Backup {'updated' if old else 'saved'} in {esc(tilde(folder))}")
        if once("second copy"):
            say("[hint]Keep a second copy somewhere else, like another drive.[/]")
        return True



# ── Kept-current backups ──────────────────────────────────────────────────────
# A dated backup is never changed. A kept-current one, "<name> (kept current)/", is the one kind that's updated:
# rebuilt whole from the card or folder each time, since one compressed file can't be patched. The new copy is
# packed, read back and given repair data in a hidden folder beside the old one, under the final names (par2
# records them), and moves in only once it checks out. A .source.json says which card or folder it's of.

KEPT = " (kept current)"


def backup_source(library: Path, card: Card | None) -> dict:
    """What a kept-current backup is of, as its .source.json records it."""
    return {"card_uuid": card.uuid} if card else {"folder": str(library.resolve())}


def read_source(folder: Path) -> dict | None:
    """A kept-current backup's .source.json, or None when the folder doesn't hold one."""
    try:
        saved = json.loads((folder / ".source.json").read_text())
    except (OSError, ValueError):
        return None
    return saved if isinstance(saved, dict) and saved.get("kept_current") is True else None


def same_source(saved: dict, source: dict) -> bool:
    if "card_uuid" in source:
        return bool(source["card_uuid"]) and saved.get("card_uuid") == source["card_uuid"]
    return isinstance(saved.get("folder"), str) and str(Path(saved["folder"]).resolve()) == source["folder"]


def find_kept(state: dict, source: dict) -> Path | None:
    """The kept-current backup of this card or folder, in the backups folder in use or the default one: the folder
    it's in. The most recently updated, should there be two."""
    found = []
    for root in dict.fromkeys([backups_from(state), DEFAULT_BACKUPS]):
        with suppress(OSError):
            for folder in root.iterdir():
                if folder.name.endswith(KEPT) and (saved := read_source(folder)) and same_source(saved, source):
                    found.append((str(saved.get("updated", "")), str(folder)))
    return Path(max(found)[1]) if found else None


def ask_backup_kind(kept: Path | None, name: str, *, can_keep: bool = True):
    """A new dated backup, or the kept-current one: "dated", "kept" or BACK."""
    width = 28
    dated = option("New dated backup", "dated", "a folder of its own; older backups stay as they are", width=width)
    if kept:
        updated = local_date((read_source(kept) or {}).get("updated")) or "on an unknown date"
        choices = [option(f"Update {kept.name}", "kept", f"last updated {updated}", width=width), dated]
    elif can_keep:
        choices = [dated, option("Start a kept-current backup", "kept", "one backup you update after each change",
                                 width=width)]
    else:
        return "dated"  # without an ID, the card's kept-current backup could never be found again
    return ask_select("Into?", [*choices, back()])


def backed_up_names(manifest: Path) -> dict[str, str] | None:
    """A backup's checksum list as path under its top folder: checksum. None when it's missing, empty or has
    lines that aren't checksums: then nothing can be told from it."""
    try:
        listed, unreadable = read_manifest(manifest)
    except OSError:
        return None
    if unreadable or not listed:
        return None
    return {nfc(name.split("/", 1)[1]): digest for name, digest in listed.items() if "/" in name}


@dataclass
class BackupChanges:
    added: list[tuple[str, int]] = field(default_factory=list)    # (album, files) new since the backup
    removed: list[tuple[str, int]] = field(default_factory=list)  # (album, files) the update drops
    renumbered: int = 0
    renamed: int = 0          # retitled albums: another title, the same files
    files_added: int = 0      # in albums both have
    files_removed: int = 0

    @property
    def removes(self) -> bool:
        return bool(self.removed or self.files_removed)


def title_keyed(names, numbering: Numbering) -> dict[tuple[str, str], str]:
    """Paths under the library's top folder keyed by (album title, rest of the path): a renumbered album matches
    itself. Albums sharing a title key by their whole folder name instead, so neither can stand in for the other;
    a file at the top, by its own name."""
    albums = {nfc(name).partition("/")[0] for name in names if "/" in name}
    shared = {title for title, count in Counter(map(numbering.album_key, albums)).items() if count > 1}
    keyed = {}
    for name in names:
        album, _, rest = nfc(name).partition("/")
        title = numbering.album_key(album)
        keyed[("/" + album.casefold() if title in shared else title, rest) if rest else ("", album)] = name
    return keyed


def numbering_of(*name_lists) -> Numbering:
    return Numbering.of(sorted({n.split("/", 1)[0] for names in name_lists for n in names if "/" in n}))


def compare_with_backup(before: list[str], after: list[str]) -> BackupChanges:
    """What an update changes, album by album, from file names alone."""
    numbering = numbering_of(before, after)
    albums = lambda names: {key[0] for key in title_keyed(names, numbering) if key[0]}
    old, new = title_keyed(before, numbering), title_keyed(after, numbering)
    old_albums, new_albums = albums(before), albums(after)
    name_of = lambda keyed, title: next(n.split("/", 1)[0] for (t, _), n in keyed.items() if t == title)
    files_in = lambda keyed, title: frozenset(rest for t, rest in keyed if t == title)
    changes = BackupChanges()
    # An album Arrange retitled has the same files under another title: renamed, not dropped and added
    arrived = {}
    for title in sorted(new_albums - old_albums):
        arrived.setdefault(files_in(new, title), []).append(title)
    renamed_from, renamed_to = set(), set()
    for title in sorted(old_albums - new_albums):
        if same := arrived.get(files_in(old, title)):
            renamed_from.add(title)
            renamed_to.add(same.pop(0))
    changes.renamed = len(renamed_from)
    for title in sorted(new_albums - old_albums - renamed_to):
        changes.added.append((name_of(new, title), sum(1 for t, _ in new if t == title)))
    for title in sorted(old_albums - new_albums - renamed_from):
        changes.removed.append((name_of(old, title), sum(1 for t, _ in old if t == title)))
    changes.renumbered = sum(1 for title in old_albums & new_albums if name_of(old, title) != name_of(new, title))
    both = lambda key: key[0] in old_albums & new_albums or not key[0]
    changes.files_added = sum(1 for key in new if both(key) and key not in old)
    changes.files_removed = sum(1 for key in old if both(key) and key not in new)
    return changes


def show_backup_changes(changes: BackupChanges, limit: int = 6) -> None:
    if not (changes.added or changes.removed or changes.renumbered or changes.renamed or changes.files_added
            or changes.files_removed):
        say("  [hint]Same albums and files as the backup; it's rebuilt to pick up any changed contents.[/]")
        return
    for album, count in changes.added[:limit]:
        say(f"  [accent]+[/] {esc(album)}  [hint]{plural(count, 'file')}[/]")
    for album, count in changes.removed[:limit]:
        say(f"  [bad]− {esc(album)}[/]  [hint]{plural(count, 'file')}, dropped from the backup[/]")
    hidden = max(0, len(changes.added) - limit) + max(0, len(changes.removed) - limit)
    if hidden:
        say(f"  [hint]… {plural(hidden, 'more album')}[/]")
    if changes.renumbered:
        say(f"  [hint]~ {plural(changes.renumbered, 'album')} renumbered[/]")
    if changes.renamed:
        say(f"  [hint]~ {plural(changes.renamed, 'album')} renamed[/]")
    if changes.files_added:
        say(f"  [accent]+[/] {plural(changes.files_added, 'file')} in albums the backup has")
    if changes.files_removed:
        say(f"  [bad]− {plural(changes.files_removed, 'file')} dropped from albums the backup has[/]")
    if changes.removes:
        warn("The update drops what's marked −. Afterwards it's only in older dated backups, if any.")


def changed_contents(before: dict[str, str], after: dict[str, str]) -> list[str]:
    """Files the backup and the new copy both have, matched by album title, whose contents differ."""
    numbering = numbering_of(before, after)
    old = {key: before[name] for key, name in title_keyed(before, numbering).items()}
    return sorted(name for key, name in title_keyed(after, numbering).items() if key in old and old[key] != after[name])


def replace_kept(folder: Path, staging: Path, before: dict[str, str] | None, source: dict) -> bool:
    """Move the checked new copy in place of the old one. A file that kept its name but changed its contents is
    most likely damage, so that has to be agreed to first. False when the old copy stays."""
    archive = next(staging.glob("*.tar.zst"))
    after = backed_up_names(sidecar(archive, ".sha256")) or {}
    if changed := (changed_contents(before, after) if before is not None else []):
        warn(f"{plural(len(changed), 'file')} kept {'its' if len(changed) == 1 else 'their'} name but changed "
             "contents since the backup:")
        listing(changed)
        say("[hint]Tracks aren't edited in place, so this is most likely damage on the card or in the folder. "
            "Check › Find damaged tracks can test them.[/]")
        if not ask_confirm("Replace the backup's copies with these anyway?", False):
            shutil.rmtree(staging, ignore_errors=True)
            say("[hint]The kept-current backup stays as it was.[/]")
            return False
    with ctrl_c_shield():  # a Ctrl-C now would leave half of each copy
        note_kept(staging, source)  # moves in with the copy, so even a first backup cut short is known as one
        names = "\n".join(sorted(path.name for path in staging.iterdir()))
        with open(staging / ".ready", "w", encoding="utf-8") as ready:  # on the drive before anything moves
            ready.write(names)
            durable(ready)
        move_in(staging, folder)
    return True


def move_in(staging: Path, folder: Path) -> None:
    """Move a checked copy in place of the old one: its files first, then the old one's that they didn't replace.
    .ready in staging lists the copy's files and says it checked out, so a move cut short (a crash, a pulled
    drive) is finished by settle_kept next time."""
    new = set((staging / ".ready").read_text(encoding="utf-8", errors="replace").splitlines())
    for name in sorted(new):
        if (staging / name).exists():  # not moved in yet
            os.replace(staging / name, folder / name)
    # The old copy's files go only once every new one is in place. A list a crash cut short names too little, and
    # trusting it would delete the old copy and the new one with it.
    if not (any(name.endswith(".tar.zst") for name in new) and all((folder / name).exists() for name in new)):
        warn(f"An update of {esc(tilde(folder))} was cut short, so nothing of its old copy was deleted. "
             "Update it again to rebuild it.")
        (staging / ".ready").unlink(missing_ok=True)
        return
    for path in folder.iterdir():
        if path.name not in new and not path.name.startswith(".") and path.name.endswith(
                (".tar.zst", ".tar.zst.sha256", ".par2")):
            path.unlink(missing_ok=True)
    (staging / ".ready").unlink(missing_ok=True)
    staging.rmdir()


def note_kept(folder: Path, source: dict) -> None:
    note = folder / ".source.json"
    temp = note.with_suffix(".tmp")
    temp.write_text(json.dumps(source | {"kept_current": True,
                                         "updated": datetime.now(UTC).isoformat(timespec="seconds")}, indent=2))
    temp.replace(note)


def settle_kept(folder: Path) -> None:
    """What a stopped update left in .new: a checked copy part-way moved in is moved the rest of the way; anything
    else there never checked out, and goes."""
    staging = folder / ".new"
    if (staging / ".ready").exists():
        warn("Finishing an update that was stopped while its new copy moved in.")
        move_in(staging, folder)
        note_kept(folder, {key: value for key, value in (read_source(folder) or {}).items() if key != "updated"})
    shutil.rmtree(staging, ignore_errors=True)


# ── Task: restore ─────────────────────────────────────────────────────────────

def task_restore(tools: Tools, state: dict):
    archive = pick_archive(state, "Restore which backup?")
    if archive is None:
        return BACK
    with doing("Restoring", archive.name):
        manifest = sidecar(archive, ".sha256")
        top = archive_top_folder(archive, manifest)

        default = tilde(state.get("restore_dir") or HOME / "Desktop" / "Tecsun Restored")
        places = [(tilde(state["restore_dir"]) + "/", "last used")] if state.get("restore_dir") else []
        places += [(tilde(p) + "/", "") for p in (HOME / "Desktop", HOME / "Music") if p.is_dir()]
        # SD cards only, looked up once (the check runs on every keystroke); other drives can hold a restore
        card_mounts = [c.mount for c in list_cards() if c.kind.startswith(("SD card", "card"))]

        def not_here(path: Path) -> str | None:
            if any(inside(path, mount) for mount in card_mounts):
                return "That's a card. Restore into a folder here, then use Add → Replace everything."
            return "That's the backup's own folder. Pick another." if inside(archive.parent, path / top) else None

        dest = ask_path("Restore into which folder?", default, places, must_exist=False, check=not_here)
        if dest is BACK:
            return BACK
        target = dest / top

        if target.exists() and any(target.iterdir()):
            warn(f"{esc(tilde(target))} already has files. Same-named ones get replaced, once every file checks out.")
            if not ask_confirm("Restore into it anyway?", False):
                outro("Nothing was restored.", good=False)
                return

        size = archive.stat().st_size
        room = free_space(dest)
        say(f"[hint]Backup[/]   {esc(tilde(archive))}")
        say(f"[hint]Into[/]     {esc(tilde(target))}")
        if manifest.is_file():
            say("[hint]Checks[/]   every file against its checksum, before anything is replaced")
        else:
            say("[hint]Checks[/]   [warn]no checksum file next to the backup, so files can't be checked one by one[/]")
        say(f"[hint]Needs[/]    about {human(size)}, {human(room)} free there")
        say()
        if size > room and not ask_confirm("Not enough room there. Start anyway?", False):
            outro("Nothing was restored.", good=False)
            return
        if ask_go(f"Restore into {target.name}") is BACK:
            outro("Nothing was restored.", good=False)
            return

        if check_parity(archive, tools, repair=True) == "failed" and not ask_confirm(
                "Unpack anyway? Damaged files get named, and nothing existing is replaced.", False):
            outro("Nothing was restored. Try another copy of this backup.", good=False)
            return

        dest.mkdir(parents=True, exist_ok=True)
        try:
            with progress_bar() as bar:
                task = bar.add_task("", total=archive.stat().st_size, detail="unpacking", note="")
                staging, skipped = unpack_to_staging(archive, dest, lambda n: bar.advance(task, n))
        except READ_ERRORS as error:
            if getattr(error, "errno", None) in (errno.ENOSPC, errno.EDQUOT, errno.EACCES, errno.EROFS):
                fail(f"Couldn't write into {esc(tilde(dest))}: {esc(str(error))}")
            else:
                fail(f"The backup couldn't be read: {esc(str(error))}")
            outro("Nothing was restored, and your existing files weren't touched.", good=False)
            return
        done("Unpacked")
        if skipped:
            warn(f"Skipped {plural(len(skipped), 'link')} pointing outside the restore folder, e.g. {esc(skipped[0])}")

        if manifest.is_file():
            try:
                total = sum(p.stat().st_size for p in staging.rglob("*") if p.is_file() and not p.is_symlink())
                with progress_bar() as bar:
                    task = bar.add_task("", total=max(total, 1), detail="checking files", note="")
                    checked = verify_files(staging, manifest, lambda n: bar.advance(task, n))
            except BaseException:
                shutil.rmtree(staging, ignore_errors=True)  # nothing was replaced yet
                raise
            if not report_checked(checked):
                kept = set_aside(staging, dest, top)
                outro(f"Not restored: some files don't match. Everything unpacked is in {esc(tilde(kept))}; "
                      "nothing existing was replaced.", good=False)
                return
        else:
            warn("No checksum file next to the backup. It unpacked cleanly, but files couldn't be checked one by one.")

        stuck = move_into_place(staging, dest)
        if stuck:
            fail("These couldn't replace what's already there (a file where a folder is, the reverse, or a file that "
                 "can't be replaced):")
            listing(stuck)
            say(f"[hint]Their restored copies are in {esc(tilde(staging))}[/]")
        os.sync()
        save_state(state, restore_dir=str(dest), last_archive=str(archive))
        if stuck:
            outro("Restored, except the items above.", good=False)
        else:
            outro(f"Restored into {esc(tilde(target))}.")



# ── Task: check ───────────────────────────────────────────────────────────────

def task_check(tools: Tools, state: dict):
    what = ask_select("Check what?", [
        option("Verify a backup", "verify", "test every file inside it, without unpacking", width=26),
        option("Find damaged tracks", "audio", "on the card or in a folder: tracks that would skip", width=26),
        option("Read the card's play order", "order", "straight off the card, and fix it if needed", width=26),
        back(),
    ])
    if what is BACK:
        return BACK
    return {"verify": check_backup, "audio": check_library_audio, "order": check_card_order}[what](tools, state)


def check_backup(tools: Tools, state: dict):
    archive = pick_archive(state, "Verify which backup?")
    if archive is None:
        return BACK
    manifest = sidecar(archive, ".sha256")
    parity = check_parity(archive, tools, repair=False)

    if not manifest.is_file():
        warn("No checksum file next to the backup. Testing that it unpacks cleanly instead.")
    try:
        with progress_bar() as bar:
            task = bar.add_task("", total=archive.stat().st_size, detail="reading every file", note="")
            checked = verify_archive(archive, manifest if manifest.is_file() else None,
                                     lambda n: bar.advance(task, n))
    except READ_ERRORS as error:
        fail(f"The backup is damaged: {esc(str(error))}")
        if parity == "damaged":
            outro("Restore can repair it from its repair data.", good=False)
        elif parity == "skipped" and not tools.par2 and sidecar(archive, ".par2").is_file():
            outro(f"It has repair data: install par2 ({install_hint('par2')}), then Restore can try to repair it.",
                  good=False)
        else:
            outro("This backup isn't usable.", good=False)
        return

    good = report_checked(checked) if manifest.is_file() else True
    if not manifest.is_file():
        done(f"Unpacks cleanly: {plural(checked.files, 'file')}")
    save_state(state, last_archive=str(archive))
    if good and parity in ("ok", "skipped"):
        outro("The backup is good.")
    else:
        fail("The backup has problems. See above.")
        outro("Checked.", good=False)


def audio_files(root: Path) -> list[Path]:
    """Every audio file under `root`, skipping hidden folders (a card's Spotlight folder can't even be listed)."""
    found = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if not d.startswith(".")]
        found += [Path(dirpath, f) for f in filenames if not f.startswith(".") and is_audio(Path(f))]
    return sorted(found, key=lambda p: natural_key(str(p)))


def ask_scan_what(card: Card) -> Path | None:
    """The whole card, or one album on it. None to go back."""
    albums = scan_card(card.mount).albums
    whole, one = object(), object()
    width = max(len(f"All of {card.name}"), len("One album…"))
    while True:
        picked = ask_select(f"Scan what on {card.name}?", [
            option(f"All of {card.name}", whole, plural(len(albums), "album"), width=width),
            *([option("One album…", one, "picked from the card", width=width)] if albums else []),
            back(),
        ])
        if picked is not one:
            return None if picked is BACK else card.mount
        if (album := pick_album(albums, "Scan which album?")) is not BACK:
            return card.mount / album


def check_library_audio(tools: Tools, state: dict):
    if not (tools.flac or tools.ffmpeg):
        fail(f"Finding damaged tracks needs flac or ffmpeg ({install_hint('flac', 'ffmpeg')}).")
        outro("Nothing was checked.", good=False)
        return
    picked = pick_card_or_folder(state, "Scan what?", "music in a folder on this computer")
    if picked is BACK:
        return BACK
    if picked == "folder":
        root = ask_path("Scan which folder?", tilde(state["library"]) if state.get("library") else "",
                        library_places(state), must_exist=True)
        if root is BACK:
            return BACK
    elif (root := ask_scan_what(picked)) is None:
        return BACK

    files = audio_files(root)
    if not files:
        fail("No audio files there.")
        outro("Nothing was checked.", good=False)
        return
    say(f"[hint]Decoding {plural(len(files), 'track')}. A damaged track shows up as a decoding error.[/]")
    report = check_audio(files, tools)
    show_audio_report(report, root, tools)
    if report.failed:
        say("[hint]Re-rip or replace the tracks above.[/]")

    if picked == "folder":
        outro("Done." if not report.failed else "Done, with damaged tracks.", good=not report.failed)
        return
    offer_finish(picked, tools, state)


def show_play_order(albums: list[str]) -> None:
    """Every album, in the order the radio plays them: reviewing the order is the point, so nothing is cut."""
    say(f"[hint]The radio plays these {plural(len(albums), 'album')} in this order:[/]")
    listing(albums, limit=len(albums), mark="[hint]·[/]")


def check_card_order(tools: Tools, state: dict):
    chosen = choose_card(state)
    if chosen is None:
        return BACK
    card, contents = chosen
    expected = visible_tree(card.mount)
    if IS_MAC:  # read while mounted: no password, and the card stays put unless it needs sorting
        actual, sudo = listed_order(card.mount), None
    else:  # fatsort reads the order off the unmounted card
        blocker = sort_blocker(card, tools)
        if blocker:
            fail(blocker)
            outro("Nothing was checked.", good=False)
            return
        say("[hint]Reading the order means unmounting the card for a moment.[/]")
        sudo = get_admin(card, tools, spotlight=False)
        if sudo is None or not take_card_offline(card, sudo):
            outro("Nothing was checked.", good=False)
            return
        actual = read_order(card, sudo)

    listed = {nfc(name) for name in contents.albums}
    read = bool(actual)  # an order that couldn't be read is unknown, not wrong
    if read:
        show_play_order([n for n in actual.get("", []) if not n.startswith(".") and nfc(n) in listed])
    problems = report_order(expected, actual, after_sort=False)
    sortable = any(p.sortable for p in problems)
    in_pieces, hidden = {}, []
    if IS_MAC:  # the other things that trip the radio up, while the card is mounted
        sudo = get_admin(card, tools, sorting=False, spotlight=False)  # asks only when the file table needs it
        in_pieces, table = find_pieces(card, sudo)
        report_pieces(card, in_pieces, table, sudo)
        if hidden := hidden_clutter(card.mount):
            warn(f"Hidden files macOS added, which the radio can take for albums: {esc(', '.join(hidden))}")
    blocker = sort_blocker(card, tools) if sortable else None
    if blocker:
        warn(blocker)
        manual_sort_hint(card)
    if IS_MAC and ((sortable and not blocker) or in_pieces or hidden):
        # mounted, it gathers hidden files again, so it's cleaned, sorted and ejected as Clean does
        if sortable:
            say("[hint]Sorting puts the card's file list in name order, the order the radio plays.[/]")
        if not in_pieces:
            say("[hint]No tracks are changed or moved.[/]")
        if card.problem() is None and ask_confirm(f"Clean, sort and eject {card.name} now?", True):
            receipt = Receipt()
            if sortable and not blocker:
                receipt.add("↕", "play order", "sorted to match the numbers")
            if hidden:
                receipt.add("−", "macOS hidden files", "removed")
            finish_card(card, tools, state, offer_backup=False, receipt=receipt)
            return
        RUN.declined.add(card_key(card))
    elif sortable and not blocker and not IS_MAC:
        say("[hint]Sorting puts the card's file list in name order, the order the radio plays.[/]")
        say("[hint]No tracks are changed or moved.[/]")
        if ask_confirm("Sort the card now?", True):
            if not device_still_matches(card):
                raise SafetyError(f"{card.device} no longer looks like {card.name}. Not sorting it.")
            if run_fatsort(card, sudo):
                after = read_order(card, sudo)
                read = bool(after)
                problems = report_order(expected, after, after_sort=True)
    if problems:
        fail("The card isn't in play order. See above." if read else "Couldn't read the play order off the card.")

    if os.path.ismount(card.mount):
        needs_clean = problems or in_pieces or hidden
        outro("Done. The card is still mounted." + (" Run Clean before it goes back in the radio." if needs_clean else ""),
              good=not (problems or in_pieces))
        return
    eject, mount = object(), object()
    after = eject
    if can_mount():  # without udisks2 it couldn't be mounted again, so it's simply ejected
        after = ask_select("Then", [option("Eject", eject, "ready to pull"), option("Mount it again", mount)],
                           on_escape=mount, esc_hint="")
    if after is mount:
        if mount_card(card):
            outro("Mounted again.")
        else:
            fail("Couldn't mount it again.")
            outro("It's unmounted, so it's safe to pull.", good=False)
    elif eject_card(card):
        outro("Ejected. Ready for the radio.")
    else:
        fail("The card didn't eject.")
        outro("It's unmounted. Eject it before you pull it out.", good=False)



# ── Task: stats ───────────────────────────────────────────────────────────────
# The card at a glance, from its file list and sizes: nothing is decoded, so it's quick.

def meter(part: float, whole: float, width: int = 20) -> Text:
    filled = min(width, round(width * part / whole)) if whole else 0
    return Text.assemble(("█" * filled, "accent"), ("░" * (width - filled), "rail"))


def stat_row(label: str, value: str | Text, width: int = 18) -> None:
    say(Text.assemble("  " + label.ljust(width), value if isinstance(value, Text) else Text.from_markup(value)))


def show_stats(card: Card, contents: CardContents, state: dict) -> None:
    root = card.mount
    sizes = {path: path.stat().st_size for path in audio_files(root)}
    formats = Counter(path.suffix.lstrip(".").upper() for path in sizes)
    per_album = Counter()
    for path, size in sizes.items():
        if len(parts := path.relative_to(root).parts) > 1:  # a track loose at the top isn't an album
            per_album[parts[0]] += size
    used = card.size - card.free

    say(f"[strong]{plural(len(contents.albums), 'album')}[/] · [strong]{plural(len(sizes), 'track')}[/] · "
        f"{human(sum(sizes.values()))}")
    say(Text.assemble("Card  ", meter(used, card.size), f"  {human(used)} of {human(card.size)}"))
    if formats:
        say()
        say("[heading]Formats[/]")
        top = formats.most_common(1)[0][1]
        for name, count in formats.most_common():
            say(Text.assemble(f"  {name:<6}", meter(count, top, 16),
                              f"  {count:>{len(f'{top:,}')},} {'track' if count == 1 else 'tracks'}"))
    if per_album:
        say()
        say("[heading]Largest albums[/]")
        shown = per_album.most_common(5)
        width = min(30, max(len(name) for name, _ in shown))
        for name, size in shown:
            say(Text.assemble("  " + short(nfc(name), width).ljust(width) + "  ", meter(size, shown[0][1], 16),
                              f"  {human(size)}"))
    say()
    backed_up = local_date(state.get("cards", {}).get(card.uuid, {}).get("backed_up"))
    stat_row("Last backup", backed_up or "[warn]none of this card on record[/]")
    if reminder := backup_reminder(state, card):
        warn(reminder)


def task_stats(tools: Tools, state: dict):
    chosen = choose_card(state, changes=False)
    if chosen is None:
        return BACK
    card, contents = chosen
    show_stats(card, contents, state)
    outro("Done.")


# ── Task: generate playlist ───────────────────────────────────────────────────
# The card's albums as a list to keep: an EPUB for the XTEINK X4, a PDF to print and fold into the radio's case,
# and a web page, written beside the script. Read from folder and file names, and each track's header for its
# play time, so it's quick and changes nothing on the card.

PLAYLIST_TITLE = "Tecsun Playlist"
PLAYLIST_NAME = "tecsun-playlist"   # the files' name unless another is typed: .epub, .pdf and .html
PLAYLIST_KINDS = (".epub", ".pdf", ".html")


@dataclass(frozen=True)
class Track:
    number: str                    # "7", or with a disc, "2.12"
    title: str
    seconds: float | None = None   # its play time; None when its header can't be read


@dataclass(frozen=True)
class Listed:
    number: str   # as the folder writes it, "07"; "" without one
    artist: str   # "" when the title has no " - "
    album: str
    tracks: tuple[Track, ...] = ()   # in play order: the EPUB's album chapters, the web page's track lists


def play_time(path: Path) -> float | None:
    """A track's play time in seconds, from its header, or None. Most MP3s record their length there; for one
    that doesn't, mutagen estimates it from the first frame's bitrate."""
    import mutagen

    try:
        audio = mutagen.File(path)
    except Exception as error:  # a malformed file can trip more than MutagenError, and a time isn't worth a stop
        LOG.info("No play time for %s: %s", path, error)
        return None
    # An untagged file reads as false (mutagen's result is a dict of its tags), so it's checked against None
    return (audio.info.length or None) if audio is not None else None


def album_tracks(folder: Path) -> tuple[Track, ...]:
    """An album's tracks in the order the radio plays them (a subfolder's before the album's own), each split
    from "07 - Title.flac" or "1-07 Title.mp3" at its number. A name without one is numbered by its place."""
    tree = visible_tree(folder)

    def played(here: str) -> list[str]:
        paths = []
        for entry in tree.get(here, []):
            path = os.path.join(here, entry) if here else entry
            paths += played(path) if path in tree else [path] if is_audio(Path(entry)) else []
        return paths

    tracks = []
    for place, path in enumerate(played(""), 1):
        stem = nfc(Path(path).stem).strip()
        seconds = play_time(folder / path)
        # "07 - Title", "07. Title", "07 Title", or with a disc, "2-07 Title" or "02.07 - Title" (shown as 2.7).
        # A year starting a title is no track number.
        match = re.match(r"(?:(\d{1,2})[-.])?0*(\d{1,3})(?:\s*[-.]\s*|\s+)(.+)", stem)
        if match:
            tracks.append(Track(f"{int(match[1])}.{match[2]}" if match[1] else match[2], match[3], seconds))
        else:
            tracks.append(Track(str(place), stem, seconds))
    return tuple(tracks)


def playlist_albums(albums: list[str], tracks: dict[str, tuple] | None = None) -> list[Listed]:
    """The card's albums in the order the radio plays them, each split from "07 - John Coltrane - My Favorite
    Things" at its number and at the first " - " of the title. Numbers are padded to one width, so they line up.
    `tracks`: each album's, by its folder's name."""
    pairs = sorted(((nfc(name), name) for name in albums), key=lambda pair: fatsort_key(pair[0]))  # macOS lists
    numbering = Numbering.of([name for name, _ in pairs])                                     # names decomposed
    split = [numbering.split(name) for name, _ in pairs]
    width = max((len(number) for number, _, _ in split), default=0)
    listed = []
    for (_, folder), (number, _, title) in zip(pairs, split):
        artist, dash, album = title.partition(" - ")
        number = number.zfill(width) if number else ""
        on_card = (tracks or {}).get(folder, ())
        listed.append(Listed(number, artist, album, on_card) if dash else Listed(number, "", title, on_card))
    return listed


def long_date(when: datetime) -> str:
    return f"{when:%B} {when.day}, {when.year}"


def xml_text(text: str) -> str:
    """Text as XML holds it: escaped, and without what XML can't hold at all: control characters, and on Linux
    the stand-ins Python uses for bytes in a name that aren't UTF-8."""
    return html.escape(re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f\ud800-\udfff\ufffe\uffff]", "", text), quote=False)


# The X4's firmware (CrossPoint 1.6.5) lays a book out in the reader's own font and size and ignores <style>
# elements, so the stylesheet is a file of its own. It starts a page at every chapter-menu entry: the list is
# one entry, then each album a chapter of its own. It breaks and justifies lines only at ASCII spaces (a no-break
# space it never breaks, but does stretch), so the spaces from its font's General Punctuation used here keep
# their width: an em space after the number, and a quarter em tying a track's number to its title and a dot to
# the title before it. Its digits differ in width, so a hair space after each narrow one keeps every artist
# starting in one place.
EM_SPACE, HAIR_SPACE, QUARTER_SPACE = "\u2003", "\u200a", "\u2005"
NARROW_DIGITS = {"1", "2", "7"}


def x4_number(number: str) -> str:
    return number + HAIR_SPACE * sum(digit in NARROW_DIGITS for digit in number) + EM_SPACE if number else ""


def x4_album_line(item: Listed) -> str:
    """An album's line, the same in the list and atop its chapter."""
    return (f'<p class="{"album" if item.number else "loose"}">{x4_number(item.number)}'
            + (f"<b>{xml_text(item.artist)}</b> – " if item.artist else "") + f"<i>{xml_text(item.album)}</i></p>\n")


def x4_tracks(item: Listed) -> str:
    """The album's tracks in one paragraph, "1 Pigs · 2 How I Could Just Kill a Man", each number in bold. A line
    breaks only after a dot or inside a title."""
    if not item.tracks:
        return ""
    run = f"{QUARTER_SPACE}· ".join(f"<b>{track.number}</b>{QUARTER_SPACE}{xml_text(track.title)}"
                                    for track in item.tracks)
    return f'<p class="tracks">{run}</p>\n'


def x4_label(item: Listed) -> str:
    """An album's chapter-menu entry: "07 Cypress Hill – Cypress Hill"."""
    return " ".join(filter(None, (item.number, f"{item.artist} – {item.album}" if item.artist else item.album)))


def x4_page(title: str, body: str) -> str:
    return ('<?xml version="1.0" encoding="utf-8"?>\n<!DOCTYPE html>\n'
            '<html xmlns="http://www.w3.org/1999/xhtml" xml:lang="en" lang="en">\n'
            f'<head><meta charset="utf-8"/><title>{xml_text(title)}</title>'
            f'<link rel="stylesheet" type="text/css" href="style.css"/></head>\n<body>\n{body}</body>\n</html>\n')


# The EPUB's cover, which the X4 shows on its home screen and, when asked, its sleep screen: black on white, at
# the X4's screen size, in the Vera Sans that comes with reportlab. The home screen shrinks it to 135 x 225 in
# pure black and white, so the title is big. Below it, the first albums, as many as fit whole, run on like an
# album's tracks, each number in a black box as on the printed card.
COVER_SIZE = (480, 800)
COVER_TYPE = 32   # the albums' type, in pixels: about five fit, readable at full size


def cover_fonts(size: int) -> dict:
    import reportlab
    from PIL import ImageFont

    folder = Path(reportlab.__file__).parent / "fonts"
    return {style: ImageFont.truetype(str(folder / name), size)
            for style, name in (("r", "Vera.ttf"), ("b", "VeraBd.ttf"), ("i", "VeraIt.ttf"))}


def cover_words(item: Listed, last: bool) -> list[list[tuple[str, str]]]:
    """An album as the words a line can break between, each a list of (style, text) runs. The number's box
    keeps to the first word, the dash to the artist and the dot to the album."""
    artist = [[("b", word)] for word in drawable(item.artist).split()]
    album = [[("i", word)] for word in drawable(item.album).split()]
    if artist and album:
        artist[-1].append(("r", " –"))
    words = artist + album or [[]]
    if not last:
        words[-1].append(("r", " ·"))
    if item.number:
        words[0][:0] = [("box", item.number), ("r", " ")]
    return words


def cover_run_width(word: list[tuple[str, str]], fonts: dict) -> float:
    pad = fonts["b"].size / 4
    return sum(fonts["b"].getlength(text) + 2 * pad if style == "box" else fonts[style].getlength(text)
               for style, text in word)


def cover_lines(listed: list[Listed], fonts: dict, width: float, room: int) -> list[list]:
    """The lines of the most whole albums that fit in `room` lines of `width` pixels."""
    space, fitted = fonts["r"].getlength(" "), []
    for count in range(1, len(listed) + 1):
        lines, used = [[]], 0.0
        for index, item in enumerate(listed[:count]):
            for word in cover_words(item, last=index == count - 1):
                needed = cover_run_width(word, fonts)
                if lines[-1] and used + space + needed > width:
                    lines.append([])
                    used = 0.0
                used += (space if lines[-1] else 0) + needed
                lines[-1].append(word)
        if len(lines) > room:
            break
        fitted = lines
    return fitted


def playlist_cover(listed: list[Listed], when: datetime) -> bytes:
    """The cover as a greyscale PNG: the title, the first albums, then how many there are and the date."""
    from PIL import Image, ImageDraw

    width, height = COVER_SIZE
    margin = 36
    image = Image.new("L", COVER_SIZE, 255)
    pen = ImageDraw.Draw(image)
    title = cover_fonts(84)["b"]
    for row, word in enumerate(PLAYLIST_TITLE.split()):
        pen.text((margin, 40 + row * 92), word, font=title, fill=0)
    rule = 40 + 92 + 104
    pen.rectangle((margin, rule, width - margin, rule + 7), fill=0)

    footer = height - 40 - 34 - 10 - 26
    pen.text((margin, footer), plural(len(listed), "album"), font=cover_fonts(34)["b"], fill=0)
    pen.text((margin, footer + 34 + 10), long_date(when), font=cover_fonts(26)["r"], fill=0)

    fonts = cover_fonts(COVER_TYPE)
    top, leading = rule + 7 + 30, round(COVER_TYPE * 1.38)
    space, pad = fonts["r"].getlength(" "), COVER_TYPE / 4
    ascent, descent = fonts["b"].getmetrics()
    lines = cover_lines(listed, fonts, width - 2 * margin, (footer - 30 - top) // leading)
    for row, line in enumerate(lines):
        x, y = margin, top + row * leading
        for word in line:
            for style, text in word:
                if style == "box":
                    box = fonts["b"].getlength(text) + 2 * pad
                    pen.rectangle((x, y - COVER_TYPE * 0.08, x + box, y + ascent + descent * 0.4), fill=0)
                    pen.text((x + pad, y), text, font=fonts["b"], fill=255)
                    x += box
                else:
                    pen.text((x, y), text, font=fonts[style], fill=0)
                    x += fonts[style].getlength(text)
            x += space
    out = io.BytesIO()
    image.save(out, "PNG", optimize=True)
    return out.getvalue()


def playlist_epub(listed: list[Listed], when: datetime, book_id: str) -> bytes:
    """The playlist as an EPUB 3 (with an NCX for older readers): a page listing the albums, an album to a
    paragraph, then a chapter for each album with its tracks. Its cover is no page, just the picture the X4
    shows for it."""
    digits = max((len(item.number) for item in listed), default=0)
    hang = f"{(digits * 0.578 + 1) * 0.912:.2f}em" if digits else "0"  # a number and its gap, in the X4's em
    css = ("p { margin: 0; text-indent: 0; }\n"
           "p.count { margin-bottom: 0.6em; }\n"
           f"p.album {{ margin-left: {hang}; text-indent: -{hang}; }}\n"
           f"p.loose {{ margin-left: {hang}; }}\n"  # no number: it starts where the artists do
           f"p.tracks {{ margin-left: {hang}; }}\n")
    page = x4_page(PLAYLIST_TITLE, f"<p><b>{PLAYLIST_TITLE}</b></p>\n<p><i>{long_date(when)}</i></p>\n"
                                   f'<p class="count">{plural(len(listed), "album")}</p>\n'
                                   + "".join(x4_album_line(item) for item in listed))
    width = max(2, len(str(len(listed))))
    chapters = [(f"a{i:0{width}d}", f"album-{i:0{width}d}.xhtml", x4_label(item),
                 x4_page(x4_label(item), x4_album_line(item) + x4_tracks(item))) for i, item in enumerate(listed, 1)]
    entries = [("list", "playlist.xhtml", PLAYLIST_TITLE)] + [(key, href, label) for key, href, label, _ in chapters]
    opf = ('<?xml version="1.0" encoding="utf-8"?>\n'
           '<package xmlns="http://www.idpf.org/2007/opf" version="3.0" unique-identifier="id" xml:lang="en">\n'
           '  <metadata xmlns:dc="http://purl.org/dc/elements/1.1/">\n'
           f'    <dc:identifier id="id">{book_id}</dc:identifier>\n'
           f"    <dc:title>{PLAYLIST_TITLE}</dc:title>\n    <dc:language>en</dc:language>\n"
           f"    <dc:date>{when.date().isoformat()}</dc:date>\n"
           f'    <meta property="dcterms:modified">{when.astimezone(UTC):%Y-%m-%dT%H:%M:%SZ}</meta>\n'
           '    <meta name="cover" content="cover"/>\n'  # how EPUB 2 readers find it
           "  </metadata>\n  <manifest>\n"
           '    <item id="cover" href="cover.png" media-type="image/png" properties="cover-image"/>\n'
           '    <item id="nav" href="nav.xhtml" media-type="application/xhtml+xml" properties="nav"/>\n'
           '    <item id="ncx" href="toc.ncx" media-type="application/x-dtbncx+xml"/>\n'
           '    <item id="css" href="style.css" media-type="text/css"/>\n'
           + "".join(f'    <item id="{key}" href="{href}" media-type="application/xhtml+xml"/>\n'
                     for key, href, _ in entries)
           + '  </manifest>\n  <spine toc="ncx">' + "".join(f'<itemref idref="{key}"/>' for key, _, _ in entries)
           + "</spine>\n</package>\n")
    nav = ('<?xml version="1.0" encoding="utf-8"?>\n<!DOCTYPE html>\n<html xmlns="http://www.w3.org/1999/xhtml" '
           'xmlns:epub="http://www.idpf.org/2007/ops" xml:lang="en" lang="en"><head><meta charset="utf-8"/>'
           f'<title>{PLAYLIST_TITLE}</title></head><body><nav epub:type="toc"><ol>'
           + "".join(f'<li><a href="{href}">{xml_text(label)}</a></li>' for _, href, label in entries)
           + "</ol></nav></body></html>\n")
    ncx = ('<?xml version="1.0" encoding="utf-8"?>\n<ncx xmlns="http://www.daisy.org/z3986/2005/ncx/" version="2005-1">'
           f'<head><meta name="dtb:uid" content="{book_id}"/></head><docTitle><text>{PLAYLIST_TITLE}</text></docTitle>'
           "<navMap>" + "".join(f'<navPoint id="{key}" playOrder="{order}"><navLabel><text>{xml_text(label)}</text>'
                                f'</navLabel><content src="{href}"/></navPoint>'
                                for order, (key, href, label) in enumerate(entries, 1))
           + "</navMap></ncx>\n")
    container = ('<?xml version="1.0" encoding="utf-8"?>\n'
                 '<container version="1.0" xmlns="urn:oasis:names:tc:opendocument:xmlns:container"><rootfiles>'
                 '<rootfile full-path="OEBPS/content.opf" media-type="application/oebps-package+xml"/>'
                 '</rootfiles></container>\n')
    out = io.BytesIO()
    with zipfile.ZipFile(out, "w") as book:
        book.writestr("mimetype", "application/epub+zip", compress_type=zipfile.ZIP_STORED)  # first, as EPUB asks
        for name, text in (("META-INF/container.xml", container), ("OEBPS/content.opf", opf),
                           ("OEBPS/nav.xhtml", nav), ("OEBPS/toc.ncx", ncx), ("OEBPS/style.css", css),
                           ("OEBPS/playlist.xhtml", page),
                           *((f"OEBPS/{href}", chapter) for _, href, _, chapter in chapters)):
            book.writestr(name, text.encode("utf-8"), compress_type=zipfile.ZIP_DEFLATED)
        book.writestr("OEBPS/cover.png", playlist_cover(listed, when), compress_type=zipfile.ZIP_STORED)  # PNG is packed
    return out.getvalue()


# The printed list: landscape US Letter, each half a card folded across its middle to 5.5 x 4.25 in, which
# tucks into the radio's case. Two columns a side; the header on the front. An album never splits across
# columns, and the fold runs through the margins. When the list fits one card, the other half is a spare copy.
# Helvetica, so nothing is embedded: it draws Windows-1252 characters, and the rest lose their accents.

def drawable(text: str) -> str:
    """Text Helvetica can draw: other characters lose their accents, or become "?"."""
    kept = []
    for char in text:
        try:
            char.encode("cp1252")
            kept.append(char)
        except UnicodeEncodeError:
            plain = unicodedata.normalize("NFKD", char).encode("cp1252", "ignore").decode("cp1252")
            kept.append(plain or "?")
    return "".join(kept)


def playlist_pdf(listed: list[Listed], when: datetime) -> tuple[bytes, int]:
    """The printed list, and how many folded cards it makes."""
    from reportlab.lib.colors import Color, black, white
    from reportlab.lib.pagesizes import landscape, letter
    from reportlab.lib.styles import ParagraphStyle
    from reportlab.lib.units import inch
    from reportlab.pdfbase.pdfmetrics import stringWidth
    from reportlab.pdfgen.canvas import Canvas
    from reportlab.platypus import Paragraph

    size = PRINT_FONT_SIZE
    grey, rule = Color(0.42, 0.42, 0.42), Color(0.5, 0.5, 0.5)
    sheet_w, sheet_h = landscape(letter)
    side_w, side_h = sheet_w / 2, sheet_h / 2
    margin_x, margin_y, gutter = 0.3 * inch, 0.25 * inch, 0.22 * inch
    col_w, col_h = (side_w - 2 * margin_x - gutter) / 2, side_h - 2 * margin_y
    body = ParagraphStyle("body", fontName="Helvetica", fontSize=size, leading=size * 1.2)
    gap = size * 0.3  # between albums

    digits = max((len(item.number) for item in listed), default=0)
    box_w = stringWidth("0" * digits, "Helvetica-Bold", size * 0.92) + size * 0.5 if digits else 0
    indent = box_w + size * 0.4 if digits else 0
    rows = [("head", Paragraph(PLAYLIST_TITLE, ParagraphStyle("title", fontName="Helvetica-Bold", fontSize=size * 1.6,
                                                               leading=size * 1.8)), ""),
            ("head", Paragraph(f"{long_date(when)} · {plural(len(listed), 'album')}",
                               ParagraphStyle("meta", fontName="Helvetica", fontSize=size * 0.85, leading=size * 1.7,
                                              textColor=grey)), "")]
    for item in listed:
        text = (f"<b>{html.escape(drawable(item.artist), quote=False)}</b> – " if item.artist else "") \
            + html.escape(drawable(item.album), quote=False)
        rows.append(("album", Paragraph(text, body), item.number))

    # Columns in reading order, four to a card: the front's left and right, then the back's.
    placed, column, used = [], 0, 0.0
    for kind, para, number in rows:
        _, height = para.wrap(col_w - (indent if kind == "album" else 0), col_h)
        height += gap if kind == "album" else 0
        if used + height > col_h and used:
            column, used = column + 1, 0.0
        placed.append((column, used, kind, para, number, height))
        used += height
    cards = column // 4 + 1

    out = io.BytesIO()
    canvas = Canvas(out, pagesize=(sheet_w, sheet_h), invariant=True)
    canvas.setTitle(PLAYLIST_TITLE)
    halves = max(cards, 2)  # one card: the other half is a spare copy
    for sheet in range(0, halves, 2):
        for half in (0, 1):
            if sheet + half >= halves:
                break
            card, left = (sheet + half) % cards, half * side_w
            for column, top, kind, para, number, height in placed:
                if column // 4 != card:
                    continue
                side, col = divmod(column % 4, 2)
                x = left + margin_x + col * (col_w + gutter)
                y = sheet_h - side * side_h - margin_y - top - height  # the row's bottom
                if kind == "album":
                    para.drawOn(canvas, x + indent, y + gap)
                    if number:
                        baseline = y + height - size  # the first line's
                        canvas.setFillColor(black)
                        canvas.rect(x, baseline - size * 0.22, box_w, size * 1.05, stroke=0, fill=1)
                        canvas.setFillColor(white)
                        canvas.setFont("Helvetica-Bold", size * 0.92)
                        canvas.drawCentredString(x + box_w / 2, baseline, number)
                else:
                    para.drawOn(canvas, x, y)
            canvas.setStrokeColor(rule)
            canvas.setFillColor(rule)
            if cards > 1:  # which card this is, in the front's top margin
                canvas.setFont("Helvetica", 6)
                canvas.drawRightString(left + side_w - margin_x, sheet_h - margin_y * 0.6,
                                       f"{PLAYLIST_TITLE} · card {card + 1} of {cards}")
            canvas.setLineWidth(0.5)
            canvas.setDash(1, 2)
            canvas.line(left + 6, side_h, left + side_w - 6, side_h)
            canvas.setFont("Helvetica", 6)
            canvas.drawString(left + 8, side_h + 2, "fold")
        canvas.setDash(4, 3)
        canvas.setLineWidth(0.7)
        canvas.line(side_w, 6, side_w, sheet_h - 6)
        canvas.setDash()
        canvas.drawString(side_w + 3, sheet_h - 12, "cut")
        canvas.showPage()
    canvas.save()
    return out.getvalue(), cards


# The web page: the printed card's look, in newspaper columns. As many 17rem columns as fit, up to four, and two
# at most in portrait; light or dark with the system. The list fills at least the first screen, then each album's
# tracks follow in the same columns, and each album in the list links to its own. One file with nothing to load,
# so it opens anywhere.
PLAYLIST_PAGE_STYLE = """
:root {
  color-scheme: light dark;
  --paper: light-dark(#ffffff, #141414);
  --ink: light-dark(#141414, #ececec);
  --muted: light-dark(#6b6b6b, #9b9b9b);
  --rule: light-dark(#d6d6d6, #353535);
  --tint: light-dark(#f0f0f0, #232323);
  --box: light-dark(#141414, #ececec);
  --box-ink: light-dark(#ffffff, #141414);
  --gutter: clamp(1rem, 4vw, 3rem);
}

*, *::before, *::after { box-sizing: border-box; }

body {
  margin: 0;
  background: var(--paper);
  color: var(--ink);
  font: 1rem/1.3 "Helvetica Neue", Helvetica, Arial, sans-serif;
  -webkit-text-size-adjust: 100%;
  padding-block: max(1.5rem, env(safe-area-inset-top)) max(2rem, env(safe-area-inset-bottom));
  padding-inline: max(var(--gutter), env(safe-area-inset-left)) max(var(--gutter), env(safe-area-inset-right));
}

/* Two columns cap near 1220 px; three or four in landscape cap at 1440 px */
main { max-width: 76rem; margin-inline: auto; }
@media (orientation: landscape) { main { max-width: 90rem; } }

/* The header and the list fill at least the first screen, with the browser's bars showing, so the tracks start
   below it. A longer list just runs on. */
.page-one { min-height: calc(100svh - max(1.5rem, env(safe-area-inset-top))); }

header { display: flex; flex-wrap: wrap; align-items: baseline; gap: 0.25em 1em; margin-block-end: 1.25em; }
h1 { margin: 0; font-size: 1.6em; line-height: 1.1; letter-spacing: -0.01em; }
header p { margin: 0; color: var(--muted); font-size: 0.85em; }

.albums, .tracks { columns: 17rem 4; column-gap: 2.5rem; }
@media (orientation: portrait) { .albums, .tracks { columns: 18rem 2; } }

a { color: inherit; text-decoration: none; }
cite { font-style: normal; }

.number {
  justify-self: start;
  background: var(--box);
  color: var(--box-ink);
  font-size: 0.92em;
  font-weight: 700;
  font-variant-numeric: tabular-nums;
  padding: 0.08em 0.27em;
  border-radius: 0.12em;
}
.blank { visibility: hidden; }

/* The list. Each album is one link to its tracks: the number box, then the title, which wraps under itself and
   not under the number. Only the album's name underlines. */
.albums { margin: 0; padding: 0; list-style: none; }
.albums li { padding-block-end: 0.55em; break-inside: avoid; text-wrap: pretty; }
.albums a {
  display: inline-grid;
  grid-template-columns: auto 1fr;
  column-gap: 0.45em;
  align-items: first baseline;
  vertical-align: top;
}
.albums a:hover cite, .albums a:focus-visible cite {
  text-decoration-line: underline;
  text-decoration-thickness: 1px;
  text-underline-offset: 0.18em;
}
.albums a:focus-visible { outline: 2px solid var(--ink); outline-offset: 3px; border-radius: 0.15em; }

/* The tracks: a rule and a heading, then each album. Its tracks' numbers line up under its number box, their
   titles under the artist, and their times at the right, under the link back up. */
.tracks { margin-block-start: 2.5em; border-block-start: 1px solid var(--rule); padding-block-start: 1.25em; }
h2 { column-span: all; margin: 0 0 1em; font-size: 1.15em; }
.tracks article {
  display: grid;
  grid-template-columns: auto 1fr auto;
  column-gap: 0.45em;
  position: relative;
  padding-block-end: 1.6em;   /* padding, not margin: a margin can push the next column's first album down */
  break-inside: avoid;
  scroll-margin-block-start: 1.25rem;
  text-wrap: pretty;
}
h3, .tracks ol, .tracks li {
  grid-column: 1 / -1;
  display: grid;
  grid-template-columns: subgrid;
  align-items: first baseline;
}
h3 { margin: 0 0 0.1em; font-size: 1em; font-weight: 400; }
h3 > a { color: var(--muted); padding-inline: 0.2em; }
h3 > a:hover, h3 > a:focus-visible { color: var(--ink); }
.tracks article > p { grid-column: 2 / -1; margin: 0 0 0.35em; color: var(--muted); font-size: 0.82em; }
.tracks ol { margin: 0; padding: 0; list-style: none; row-gap: 0.12em; font-size: 0.88em; }
.tracks li > span { justify-self: end; color: var(--muted); font-variant-numeric: tabular-nums; }

/* The album the list jumped to, tinted */
.tracks article:target::before {
  content: "";
  position: absolute;
  inset: -0.5em -0.5em 1.1em;
  z-index: -1;
  background: var(--tint);
  border-radius: 0.15em;
}
"""


def clock(seconds: float) -> str:
    """A play time as a CD player shows it: "4:07", or past an hour, "1:02:07"."""
    hours, rest = divmod(round(seconds), 3600)
    return f"{hours}:{rest // 60:02d}:{rest % 60:02d}" if hours else f"{rest // 60}:{rest % 60:02d}"


def web_album_line(item: Listed, digits: int) -> str:
    """An album's number box and title, the same in the list and atop its tracks. A box without a number keeps
    the titles in line. The no-break space keeps the dash with the artist, so no line starts with it."""
    box = (f'<span class="number">{item.number}</span>' if item.number
           else f'<span class="number blank" aria-hidden="true">{"0" * digits}</span>')
    album = f"<cite>{xml_text(item.album)}</cite>"
    return f"{box}<span><b>{xml_text(item.artist)}</b>&nbsp;– {album}</span>" if item.artist else box + album


def web_tracks(item: Listed) -> str:
    """The album's track count and total time, then each track as its number, its title and its time. A total
    is left off when any track's time is missing."""
    if not item.tracks:
        return ""
    times = [track.seconds for track in item.tracks]
    total = f" · {clock(sum(times))}" if None not in times else ""
    rows = "".join(f"        <li><span>{track.number}</span>{xml_text(track.title)}"
                   + (f"<span>{clock(track.seconds)}</span>" if track.seconds is not None else "") + "</li>\n"
                   for track in item.tracks)
    return f"      <p>{plural(len(item.tracks), 'track')}{total}</p>\n      <ol>\n{rows}      </ol>\n"


def playlist_html(listed: list[Listed], when: datetime) -> str:
    """The list as one web page: each album's number in a box, then the artist in bold, linked to the album's
    tracks further down."""
    digits = max((len(item.number) for item in listed), default=0)
    width = max(2, len(str(len(listed))))
    anchors = [f"album-{index:0{width}d}" for index in range(1, len(listed) + 1)]
    rows = "".join(f'      <li><a href="#{anchor}">{web_album_line(item, digits)}</a></li>\n'
                   for anchor, item in zip(anchors, listed))
    albums = "".join(f'    <article id="{anchor}">\n'
                     f'      <h3>{web_album_line(item, digits)}<a href="#top" aria-label="Back to the album list">↑</a>'
                     f"</h3>\n{web_tracks(item)}    </article>\n" for anchor, item in zip(anchors, listed))
    return ('<!doctype html>\n<html lang="en">\n<head>\n<meta charset="utf-8">\n'
            '<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">\n'
            f'<meta name="color-scheme" content="light dark">\n<title>{PLAYLIST_TITLE}</title>\n'
            f"<style>{PLAYLIST_PAGE_STYLE}</style>\n</head>\n<body>\n<main>\n"
            '  <div class="page-one">\n'
            f"    <header>\n      <h1>{PLAYLIST_TITLE}</h1>\n"
            f"      <p>{long_date(when)} · {plural(len(listed), 'album')}</p>\n    </header>\n"
            f'    <ol class="albums">\n{rows}    </ol>\n  </div>\n'
            f'  <section class="tracks">\n    <h2>Tracks</h2>\n{albums}  </section>\n'
            "</main>\n</body>\n</html>\n")


def playlist_files(name: str) -> tuple[Path, ...]:
    return tuple(PLAYLIST_FOLDER / f"{name}{kind}" for kind in PLAYLIST_KINDS)


def playlist_name_problem(raw: str):
    """Why a typed name won't do, or True. All three files take it, so it has no extension."""
    name = raw.strip()
    if not name:
        return "Type a name."
    if name.startswith("."):
        return "A name that starts with a dot is hidden. Pick another."
    if re.search(r"[/\\:]", name):
        return "A name can't hold / \\ or :."
    if name.casefold().endswith(PLAYLIST_KINDS):
        return "Leave off the extension: .epub, .pdf and .html are all written."
    if len(name.encode()) > 200:
        return "That name is too long."
    if any(path.is_dir() for path in playlist_files(name)):
        return "A folder has that name. Pick another."
    return True


def ask_playlist_name():
    """The files' name: PLAYLIST_NAME, replacing the last set, or another one typed, for a set of its own."""
    there = [path for path in playlist_files(PLAYLIST_NAME) if path.exists()]
    when = datetime.fromtimestamp(max(path.stat().st_mtime for path in there)).date().isoformat() if there else ""
    other = object()
    picked = ask_select("Save as", [
        option(f"{PLAYLIST_NAME}.epub, .pdf and .html", PLAYLIST_NAME,
               f"replaces the set from {when}" if there else "new"),
        divider(),
        action_choice("Another name…", other, "+", hint="a new set; the last one stays"),
        back(),
    ])
    if picked is not other:
        return picked
    while True:
        typed = typed_field("Name them", "no extension", default=f"{PLAYLIST_NAME}-{datetime.now().date().isoformat()}",
                            validate=playlist_name_problem)
        if typed is BACK:
            return BACK
        name = typed.strip()
        _answered("Name them", name)
        if not any(path.exists() for path in playlist_files(name)) or \
                ask_confirm(f"Replace {name}.epub, .pdf and .html?", False):
            return name


def write_playlist(name: str, listed: list[Listed], when: datetime, book_id: str) -> int:
    """All three files, each written under a hidden temporary name and moved in only once all are written, so a
    failed write never leaves a new EPUB beside an old PDF. How many folded cards the PDF makes."""
    pdf, cards = playlist_pdf(listed, when)
    data = (playlist_epub(listed, when, book_id), pdf, playlist_html(listed, when).encode("utf-8"))
    targets = playlist_files(name)
    if folder := next((path for path in targets if path.is_dir()), None):  # os.replace can't take its place
        raise IsADirectoryError(errno.EISDIR, "a folder has that name", str(folder))
    temps = [path.with_name(f".{path.name}.part") for path in targets]
    try:
        for temp, content in zip(temps, data):
            with open(temp, "wb") as out:
                out.write(content)
                out.flush()
                os.fsync(out.fileno())
        for temp, target in zip(temps, targets):
            os.replace(temp, target)
    finally:
        for temp in temps:
            temp.unlink(missing_ok=True)
    return cards


def task_playlist(tools: Tools, state: dict):
    chosen = choose_card(state, changes=False)
    if chosen is None:
        return BACK
    card, contents = chosen
    with busy("Reading the tracks"):
        tracks = {name: album_tracks(card.mount / name) for name in contents.albums}
    listed = playlist_albums(contents.albums, tracks)
    if not listed:
        warn("There are no albums on the card to list.")
        outro("Nothing was written.", good=False)
        return
    say(f"Lists {plural(len(listed), 'album')} in play order: each one's number, artist and album, from its "
        "folder's name. The EPUB and the web page add each album's tracks, from their file names, and the web "
        "page their play times.")
    numbers = [int(item.number) for item in listed if item.number]
    if numbers != list(range(1, len(numbers) + 1)):
        warn("Some album numbers repeat or skip. Arrange › Fix numbering puts them in order.")
    if loose := sum(not item.number for item in listed):
        say(f"[hint]{plural(loose, 'album')} without a number {'is' if loose == 1 else 'are'} listed where the radio "
            f"plays {'it' if loose == 1 else 'them'}.[/]")
    name = ask_playlist_name()
    if name is BACK:
        return BACK

    when = datetime.now().astimezone()
    book_id = f"urn:uuid:{uuid.uuid5(uuid.NAMESPACE_URL, 'tecsun-manager playlist ' + (card.uuid or card.name))}"
    try:
        with busy("Writing the playlist"):
            cards = write_playlist(name, listed, when, book_id)
    except OSError as error:
        fail(f"The playlist couldn't be written in {esc(tilde(PLAYLIST_FOLDER))}: {esc(error.strerror or str(error))}.")
        outro("Nothing was written.", good=False)
        return
    done(f"Wrote {esc(name)}.epub, .pdf and .html, beside the script")
    say(f"[hint]For the X4: copy {esc(name)}.epub onto its SD card.[/]")
    fold = "the other half is a spare copy" if cards == 1 else f"it makes {plural(cards, 'folded card')}"
    say(f"[hint]To print: {esc(name)}.pdf at 100%, not fit to page. Cut the sheet down the middle and fold a half "
        f"across its middle; {fold}.[/]")
    say(f"[hint]To view: open {esc(name)}.html in a browser.[/]")
    outro("Done.")



# ── Help and menu ─────────────────────────────────────────────────────────────

TAGLINE = "Manage the Tecsun PL-990x's SD card and its backups"
ABOUT = ("Add, arrange and clean the albums on the radio's card, kept in the order the radio plays them. "
         "Back the card up into checked archives, and restore from them.")
TASK_HINTS = {
    "add": "copy new albums onto the card, each at its number",
    "arrange": "move, rename or delete albums; the rest renumber",
    "clean": "remove macOS hidden files, re-sort, eject",
    "backup": "the card or a folder, into an archive",
    "restore": "unpack a backup and check every file",
    "check": "backups, damaged tracks, play order",
    "stats": "albums, tracks and formats at a glance",
    "playlist": "the albums as a list, for the X4, print and web",
}


@dataclass(frozen=True)
class HelpPage:
    title: str
    hint: str            # its line in the list of topics
    about: str           # what it's for, in a sentence or three
    sections: tuple = ()  # (label, rows); a row is (left, right) in two columns, or a line of text


HELP_PAGES = {  # one per task, in menu order
    "add": HelpPage(
        "Add albums", "",
        "Copies the albums in a folder onto the card, each at the place its number says, and renumbers the albums "
        "after it. Tracks already on the card aren't copied again, unless their size changed. Replace everything "
        "erases the card first, then copies the folder's albums under their own names.",
        (("Run directly", ((f"{PROG} --add", "pick the card and the folder as you go"),)),
         ("Good to know", ("Put just the new albums in a folder, numbered where they go, like 05 - Album.",
                           "If an album already has that number, it asks where the new one goes.",
                           ("On FAT32, the card's small gaps are filled with a throwaway file while it copies, so each "
                            "track lands in one piece and the radio doesn't skip it. That reads the card's file table, "
                            "which needs your password, so Add asks for it before copying."),
                           "Afterwards it offers a backup, then cleans, sorts and ejects the card.")))),
    "arrange": HelpPage(
        "Arrange albums", "",
        "Moves, renames or deletes albums on the card, and renumbers the rest so the play order stays right. "
        "Only folder names change, so it takes seconds.",
        (("Run directly", ((f"{PROG} --arrange", "pick the card as you go"),)),
         ("Good to know", ("Nothing changes until you apply the whole list; No or Esc goes back to it.",
                           "Before deleting an album it offers a fresh backup of the card.")))),
    "clean": HelpPage(
        "Clean the card", "",
        "Removes the hidden files macOS adds when the card is plugged in, finds tracks stored in scattered pieces, "
        "sorts the card into play order and ejects it.",
        (("Run directly", ((f"{PROG} --clean", "pick the card as you go"),)),
         ("Good to know", (("Run it after plugging the card in to look at it: the radio can take those hidden "
                           "folders for albums."),
                           ("The radio skips a track stored in pieces, though the file is fine. On FAT32, Clean offers "
                            "to rewrite each in one piece, and replaces it only with a copy checked against it."),
                           ("Finding every one reads the card's file table, which needs your password; on exFAT "
                            "only a quick check is possible."),
                           "Sorting uses fatsort, which may ask for your password.",
                           ("From the menu, a task that cleans the card asks whether to eject it or keep it mounted "
                            "for the next task. A card any task leaves mounted gets a yellow menu item to clean and "
                            "eject it, and Quit asks."))))),
    "backup": HelpPage(
        "Back up", "",
        "Packs the card, or a folder, into one archive with checksums, reads it back from the drive to check every "
        "file, then adds repair data. Into a new dated folder, or into the card's or folder's kept-current backup.",
        (("Run directly", ((f"{PROG} --backup", "pick the card or a folder, and where to save it"),)),
         ("Saved in <backups folder>/<date>/", (("<name>.tar.zst", "the albums: a standard tar, compressed"),
                                                ("<name>.tar.zst.sha256", "checksums"),
                                                ("<name>.tar.zst.par2", "repair data, with par2"))),
         ("Kept current", (("A kept-current backup, in <backups folder>/<name> (kept current)/, is the one you update "
                            "after each change instead of adding another. It's rebuilt whole each time: it re-reads "
                            "the card, and needs room for two copies until the new one checks out."),
                           ("Before updating it lists what changes. When albums or files would be dropped, Enter "
                            "means No; when a file kept its name but changed, it asks before replacing the backup's "
                            "copy."),
                           ("After Add or Arrange, the backup offered is the kept-current one when the card has one. "
                            "Before deleting albums it's always a new dated backup."))),
         ("Good to know", ("Each dated backup gets a new folder, and is never changed, except when Restore repairs it.",
                           ("The menu says when this script has changed a card's albums since its last backup. "
                            "Changes made in Finder aren't known."),
                           ('"Save the backup where?" starts at the backups folder in use. Type another to change '
                            "it; it's remembered."))))),
    "restore": HelpPage(
        "Restore", "",
        "Unpacks a backup into a folder on this computer and checks every file against its checksum. Files already "
        "there are replaced only once everything checks out. A backup without its checksum file is only checked "
        "for unpacking cleanly.",
        (("Run directly", ((f"{PROG} --restore", "pick the backup and the folder as you go"),)),
         ("Good to know", (("To put a backup back on the card, restore it, then use Add albums and Replace "
                           "everything on the restored folder."),
                           "It also reads .tar.xz, .tar.bz2 and .tar.gz backups.")))),
    "check": HelpPage(
        "Check", "",
        "Verifies a backup without unpacking it, finds damaged tracks on the card (all of it or one album) or in a "
        "folder, or reads the card's play order and fixes it.",
        (("Run directly", ((f"{PROG} --check", "pick what to check as you go"),)),
         ("Good to know", (("On macOS the play order is read with the card mounted; fixing it cleans, sorts and "
                           "ejects the card."),
                           ("On macOS, reading the order also names hidden files and tracks stored in pieces, which "
                            "the radio skips. Finding every one of those needs your password."))))),
    "stats": HelpPage(
        "Stats", "",
        "The card at a glance: albums and tracks, how full it is, its formats and largest albums, each with a "
        "bar, and when it was last backed up. Nothing is decoded, so it's quick.",
        (("Run directly", ((f"{PROG} --stats", "pick the card as you go"),)),)),
    "playlist": HelpPage(
        "Generate playlist", "",
        "The card's albums as a list to keep: each one's number, artist and album, from its folder's name. An EPUB "
        "to read on the XTEINK X4, with a cover of the first albums and a chapter of tracks for each album; a PDF "
        "to print and fold into the radio's case; and a web page with each album's tracks and play times. "
        "Nothing on the card changes.",
        (("Run directly", ((f"{PROG} --playlist", "pick the card as you go"),)),
         ("Good to know", ((f"The files go beside the script as {PLAYLIST_NAME}.epub, .pdf and .html, replacing "
                            "the last set. Another name… keeps the old set."),
                           ("Copy the EPUB onto the X4's SD card. The X4 doesn't notice a book replaced under the "
                            "same name, so give a newer list another name."),
                           ("Print the PDF at 100%, not fit to page. Cut the sheet down the middle, then fold a half "
                            "across its middle into a card. When the list fits one card, the other half is a spare."),
                           ("Open the web page in any browser. The album list fills the first screen, and each album "
                            "in it links to its tracks further down."))))),
}

def logs_note(state: dict) -> str:
    """The logs, said for help: what they hold, their limit, and whether they're on."""
    if not state.get("debug_log", True):
        return "a log of each run, when Debug logging is on in Settings; it's off"
    return (f"a log of each run: what it showed, asked and ran, for working out what went wrong. "
            f"About {human(LOGS_SPACE)} in all, the oldest logs deleted as each run starts; Settings turns it off")


def help_topics(state: dict) -> tuple[HelpPage, ...]:
    """The topics after the tasks. Built when shown, so they name the backups folder in use."""
    return (
        HelpPage(
            "Keys", "moving around the questions",
            "The same keys work in every question.",
            (("Keys", (("↑ ↓  Enter", "move, pick"),
                       ("type", "filter a long list; what you've typed shows under the question"),
                       ("Backspace", "edit the filter"),
                       ("y  n", "answer a yes/no question; Enter takes the default"),
                       ("Esc", ("go back: Back in a list, No on most yes/no questions, Quit at the menu; a typed "
                                "filter is cleared first")),
                       ("Tab", "complete a typed path"),
                       ("under the line", "actions, not things listed: → looks elsewhere, ← goes back, ↻ rescans"),
                       ("Ctrl-C", ("stop; while albums are sorted, renamed or deleted, or the card reformatted, it "
                                   "waits until that's done")),
                       ("yellow", "a card left mounted: cleans and ejects it"))),)),
        HelpPage(
            "Backups and safety", "play order, backups, and what's checked before writing",
            "The radio plays albums in the order they sit on the card, not by name. The number at the front of each "
            "folder name sets the order you want, and fatsort writes it onto the card after every change.",
            (("Before writing", ("The card is confirmed, then checked again before every write.",
                                 ("Before a change, it asks if you want to go ahead. The first answer spells out the "
                                  "change, and the second is Back. When the change deletes albums or drops files "
                                  "from a kept-current backup, the highlight starts on Back, so Enter right away "
                                  "cancels."),
                                 "After a change, a box lists what changed on the card.",
                                 "Deleting an album asks first and offers a backup.",
                                 "Tracks are copied under a temporary name, then renamed.",
                                 "An e-reader's card is greyed out: cleaning it would delete its reading progress.")),
             ("Before it goes back in the radio", (
                 "A card a task left mounted is named, with what could trip the radio up, and Quit offers to clean it.",
                 "A rewritten track takes the original's place only once it reads back the same, in one piece.",
                 "A stopped run says which cards still need cleaning.")),
             ("Backups", ("Each backup is read back from the drive before it counts.",
                          ("Restore unpacks into a hidden folder first and replaces nothing until every file checks "
                          "out."))))),
        HelpPage(
            "Files and settings", "what it remembers, and the tools it uses",
            "It remembers the last folders, card and backup, when each card's albums last changed and when it was "
            "backed up, and where backups go.",
            (("Files", ((tilde(STATE_FILE), ("all of that, a backups folder you picked, and your settings; delete it "
                                             "to forget them")),
                        (tilde(logs_folder()), logs_note(state)),
                        (tilde(backups_from(state)), backups_note(state)),
                        'Type another backups folder at "Save the backup where?" to change it.')),
             ("Settings", ("Debug logging: the menu's Settings turns the log of each run on or off.",
                           ("Keep scrollback: on, everything stays in the terminal, and a line with the time marks "
                            "each return to the menu after a task. Off, each pick from the menu clears the window and "
                            "its scrollback."),
                           ("Audio file types, repair-data percentage, compression level, where backups and "
                            "playlists go, and the printed playlist's type size sit at the top of tecsun-manager.py."))),
             ("Tools", (("fatsort", "play order; the one that matters most"),
                        ("par2", "repair data for backups"),
                        ("flac or ffmpeg", "finding damaged tracks"))))),
    )


def help_header(overview: bool = True) -> None:
    page_break()
    head = Text.assemble(("┌", "rail"), "  ", ("Tecsun Manager", "bold"), (" · Help", "accent"))
    version = Text(f"v{VERSION}", style="version")
    console.print(head + Text(" " * max(2, min(console.width, 80) - head.cell_len - version.cell_len)) + version)
    if overview:
        say(TAGLINE)
        say()
        say(ABOUT)
    say()


def column_lines(rows, room: int, widest: int = 32) -> list[str]:
    """Help rows as markup lines `room` wide: (left, right) pairs in two columns, the right wrapping within
    its column; a left too long for the column with its right under it; and text, as a bullet. The column fits
    the lefts no longer than `widest`."""
    width = max((len(row[0]) for row in rows if isinstance(row, tuple) and len(row[0]) <= widest), default=0)
    lines = []
    for row in rows:
        if isinstance(row, str):
            lines += [f"{'[heading]•[/]' if i == 0 else ' '} {esc(part)}" for i, part in enumerate(textwrap.wrap(row, room - 2))]
            continue
        left, right = row
        parts = textwrap.wrap(right, max(20, room - width - 2))
        if len(left) > width:
            lines.append(f"[term]{esc(left)}[/]")
            first = " " * width
        else:
            first = left.ljust(width)
        lines += [f"[term]{esc(first if i == 0 else ' ' * width)}[/]  {esc(part)}" for i, part in enumerate(parts)]
    return lines


def show_help_page(page: HelpPage) -> None:
    say(f"[accent][bold]Help › {esc(page.title)}[/][/]")
    say()
    say(esc(page.about))
    for label, rows in page.sections:
        say()
        say(f"[heading]{esc(label)}[/]")
        for line in column_lines(rows, min(console.width, 80) - 5):
            say(f"  {line}")
    say()


def help_menu(state: dict) -> None:
    """The menu's Help: the overview, then a page per topic, until Esc or Close help."""
    help_header()
    topics = [(TASK_TITLES[key], hint, HELP_PAGES[key]) for key, hint in TASK_HINTS.items()]
    topics += [(t.title, t.hint, t) for t in help_topics(state)]
    width = max(len(label) for label, _, _ in topics)
    try:
        while True:
            RUN.task = "Help"
            page = ask_select("Which topic?", [*(option(label, page, hint, width=width) for label, hint, page in topics),
                                               divider(), back("Close help")], echo=False,
                              esc_hint="Esc closes help")
            if page is BACK:
                return
            if RUN.clean_pages:  # Keep scrollback off: each topic, and the topics again, on a clean window
                clear_screen()
                help_header(overview=False)
            show_help_page(page)
            RUN.task = f"Help › {page.title}"
            topics_again = object()
            if ask_select("Where to?", [action_choice("Back to topics", topics_again, "←"), option("Close help", BACK)],
                          echo=False, on_escape=topics_again) is BACK:
                return
            if RUN.clean_pages:
                clear_screen()
                help_header()
    finally:
        RUN.task = ""


def settings_menu(state: dict) -> None:
    """Settings, from the menu: whether each run is logged, and whether earlier pages stay in scrollback."""
    RUN.task = "Settings"
    picked = None
    try:
        while True:
            on = state.get("debug_log", True)
            keep = state.get("keep_scrollback", True)
            logs = saved_logs()
            hint = (f"{plural(len(logs), 'log')} kept, {human(sum(log_size(log) for log in logs))}" if on and logs
                    else "a log of each run, for working out what went wrong")
            picked = ask_select("Which setting?", [
                option(f"Debug logging: [{'on' if on else 'off'}]", "debug_log", hint, width=22),
                option(f"Keep scrollback: [{'on' if keep else 'off'}]", "keep_scrollback",
                       "earlier pages stay above, to scroll back to" if keep else "each task starts on a clean screen",
                       width=22),
                divider(),
                back(),
            ], default=picked, echo=False)
            if picked is BACK:
                return
            if picked == "keep_scrollback":
                keep_scrollback(state, not keep)
            else:
                (logging_off if on else logging_on)(state)
    finally:
        RUN.task = ""


def keep_scrollback(state: dict, keep: bool) -> None:
    """On: every page stays in the terminal, below a line with its time. Off: each pick from the menu clears the
    window and its scrollback first. Either way, from now on."""
    LOG.info("Keep scrollback turned %s in Settings", "on" if keep else "off")
    saved = save_state(state, keep_scrollback=keep)
    RUN.clean_pages = not keep
    if not keep:
        clear_screen()
    header()
    say()
    if keep:
        done("Keep scrollback is on: earlier pages stay above, each below a line with its time.")
    else:
        done("Keep scrollback is off: each pick from the menu clears the window, so only that task is there.")
    if not saved:
        warn(f"That couldn't be saved in {esc(tilde(STATE_FILE))}, so it's {'on' if keep else 'off'} for this run "
             "only.")
    say()


def log_size(log: Path) -> int:
    try:
        return log.stat().st_size
    except OSError:
        return 0


def logging_off(state: dict) -> None:
    """This run's log stops now, and the logs kept so far can go too. No question when there are none."""
    LOG.info("Debug logging turned off in Settings")
    stop_log()
    saved = save_state(state, debug_log=False)
    logs = saved_logs()
    size = sum(log_size(log) for log in logs)
    if logs and ask_confirm(f"Delete the {plural(len(logs), 'log')} kept so far ({human(size)})?", True):
        for log in logs:
            with suppress(OSError):
                log.unlink()
        done(f"Debug logging is off, and {plural(len(logs), 'log')} deleted.")
    else:
        done("Debug logging is off." + (" The logs kept so far stay." if logs else ""))
    if not saved:
        warn(f"That couldn't be saved in {esc(tilde(STATE_FILE))}, so it's off for this run only.")
    say()


def logging_on(state: dict) -> None:
    """This run is logged from here on, and every run after."""
    saved = save_state(state, debug_log=True)
    start_log(RUN.argv)
    if RUN.log:
        done(f"Debug logging is on. This run is logged from now on, in {esc(tilde(RUN.log))}.")
    else:
        warn(f"Debug logging is on, but {esc(tilde(logs_folder()))} can't be written.")
    if not saved:
        warn(f"That couldn't be saved in {esc(tilde(STATE_FILE))}, so it's on for this run only.")
    say()


def print_help() -> None:
    """--help: the overview and every flag on one screen. The menu's Help has a page for each task."""
    console.print(f"[bold]Tecsun Manager[/] [version]v{VERSION}[/]")
    console.print(TAGLINE)
    console.print()
    console.print(ABOUT)
    console.print()
    console.print("[heading]Tasks[/]  [hint]one at a time[/]")
    for key, hint in TASK_HINTS.items():
        console.print(f"  [term]--{key:<9}[/][bold]{TASK_TITLES[key]:<18}[/]{hint}")
    console.print()
    console.print("[heading]Options[/]")
    for line in column_lines((("-h, --help", "this screen"), ("-V, --version", "the version")),
                             min(console.width, 80) - 2, widest=16):
        console.print(f"  {line}")
    console.print()
    console.print("Run it with no options for the menu. Its Help has a page for each task.")
    console.print(f"[hint]More in {esc(tilde(Path(__file__).resolve().parent / 'MANUAL.md'))}[/]")


# The menu, by what a task does: change the card, back it up, or tell you about it. Help, Settings and Quit
# sit below a line.
MENU_GROUPS = (("On the card", ("add", "arrange", "clean")), ("Backups", ("backup", "restore")),
               ("Info", ("check", "stats", "playlist")))
TASKS = {"add": task_add, "arrange": task_arrange, "clean": task_clean, "backup": task_backup,
         "restore": task_restore, "check": task_check, "stats": task_stats, "playlist": task_playlist}
TASK_TITLES = {"add": "Add albums", "arrange": "Arrange albums", "clean": "Clean the card", "backup": "Back up",
               "restore": "Restore", "check": "Check", "stats": "Stats", "playlist": "Generate playlist"}


def run_task(name: str, tools: Tools, state: dict):
    RUN.task, RUN.task_failed = TASK_TITLES[name], False
    try:
        return TASKS[name](tools, state)
    finally:
        RUN.task = ""


def clean_page(picked) -> None:
    """Keep scrollback off: each pick from the menu clears the window and its scrollback, so a task's result
    stays in view until the next pick. Quit doesn't, so the last result stays once the script ends."""
    if not RUN.clean_pages or picked is QUIT:
        return
    clear_screen()
    header()
    say()


def menu(tools: Tools, state: dict) -> None:
    """The menu, until Quit: a task that finishes, or is backed out of, comes back to it. Above it, any card
    plugged in that changed since its last backup is named. A card a task left mounted gets an item of its own,
    in yellow, to clean and eject it; Quit offers that too."""
    RUN.in_menu = True
    while True:
        for reminder in backup_reminders(state):
            warn(reminder)
        picked = ask_select("What do you want to do?", [
            *(choice for heading, names in MENU_GROUPS
              for choice in (group(heading), *(option(TASK_TITLES[n], n, TASK_HINTS[n], width=19) for n in names))),
            group(),
            *(action_choice(f"Clean and eject {card.name}", card, "⏏", style="warn",
                            hint="still mounted; ready it for the radio") for card in cards_left_mounted()),
            option("Help", "help", "what each task does", width=19),
            option("Settings", "settings", "logging, scrollback", width=19),
            option("Quit", QUIT, width=19),
        ], on_escape=QUIT, esc_hint="", on_pick=clean_page)
        if picked is QUIT:
            if not before_quitting(tools, state):
                outro("Bye.")
            return
        if picked == "help":
            help_menu(state)
            say()
            continue
        if picked == "settings":
            settings_menu(state)
            continue
        if isinstance(picked, Card):
            RUN.task, RUN.task_failed = TASK_TITLES["clean"], False
            try:
                finish_card(picked, tools, state, offer_backup=False, eject_now=True)
            finally:
                RUN.task = ""
            console.print()
            intro(tools)
            continue
        if run_task(picked, tools, state) is BACK:
            say()
        else:  # the task closed its block with └; the menu opens the next one
            console.print()
            intro(tools)


def parse_args(argv: list[str]) -> str | None:
    """One flag at most: a task, --help or --version. None means the menu. -h or --help anywhere shows help,
    whatever else is there, short flags run together (-hV) included."""
    if any(word == "--help" or re.fullmatch(r"-[A-Za-z]*h[A-Za-z]*", word) for word in argv):
        return "help"
    parser = build_parser()
    args, extra = parser.parse_known_args(argv)
    if extra:
        raise argparse.ArgumentError(None, unknown_words(extra, parser))
    return args.action


def unknown_words(extra: list[str], parser: argparse.ArgumentParser) -> str:
    """What to say about words the parser didn't take: a mistyped option, with the likely one, or a path."""
    options = [flag for action in parser._actions for flag in action.option_strings]  # argparse has no public list
    for word in extra:
        if word.startswith("-"):
            close = difflib.get_close_matches(word.split("=")[0], options, n=1)
            return f"There's no {word} option." + (f" Did you mean {close[0]}?" if close else "")
    return "It takes no paths: each task asks for its card or folder."


def build_parser() -> argparse.ArgumentParser:
    # no abbreviations: a new option could change what a shortened one means
    parser = argparse.ArgumentParser(prog="tecsun-manager", add_help=False, exit_on_error=False, allow_abbrev=False)
    one_of = parser.add_mutually_exclusive_group()
    for name in TASKS:
        one_of.add_argument(f"--{name}", dest="action", action="store_const", const=name)
    one_of.add_argument("-h", "--help", dest="action", action="store_const", const="help")
    one_of.add_argument("-V", "--version", dest="action", action="store_const", const="version")
    return parser


def main(argv: list[str] | None = None) -> int:
    RUN.reset()
    try:
        action = parse_args(sys.argv[1:] if argv is None else argv)
    except argparse.ArgumentError as error:
        errors.print(f"[bad]{esc(str(error))}[/]")
        errors.print(f"[hint]{PROG} --help lists the options.[/]")
        return 2
    if action == "help":
        print_help()
        return 0
    if action == "version":
        print(f"tecsun-manager {VERSION}")
        return 0
    if not (IS_MAC or sys.platform.startswith("linux")):
        errors.print("[bad]tecsun-manager runs on macOS and Linux.[/]")
        return 2
    if not all(stream is not None and stream.isatty() for stream in (sys.stdin, sys.stdout)):
        print_help()
        errors.print("[warn]tecsun-manager asks questions as it goes, so run it in a terminal.[/]")
        return 2

    RUN.argv = sys.argv[1:] if argv is None else argv
    state = load_state()
    if state.get("debug_log", True):
        start_log(RUN.argv)
    else:
        stop_log()
    tools = Tools.detect()
    for sig in (signal.SIGTERM, signal.SIGHUP):  # stop as Ctrl-C does, so the cleanup on the way out runs
        signal.signal(sig, stop_on_signal)
    try:
        if action:  # a task from the command line is one page, so it always stays in scrollback
            intro(tools)
            if run_task(action, tools, state) is BACK:
                outro("Nothing changed.")
            if cards_waiting():  # the task's block is closed: the question gets one of its own
                console.print()
                page_break()
                console.print(Text.assemble(("┌", "rail"), "  ", ("Before quitting", "bold")))
                say()
                before_quitting(tools, state)
        else:
            RUN.clean_pages = not state.get("keep_scrollback", True)
            intro(tools)
            menu(tools, state)
        return 1 if RUN.failed else 0
    except (KeyboardInterrupt, EOFError) as stop:  # EOFError: Ctrl-D in an empty field
        errors.print()
        signum = getattr(stop, "signum", signal.SIGINT)
        return stopped("Cancelled." if signum == signal.SIGINT else f"Stopped by {signal.Signals(signum).name}.",
                       128 + signum)
    except SafetyError as error:
        fail(esc(str(error)))
        return stopped("Stopped to be safe.", 1)
    except OSError as error:
        fail(esc(f"{error.strerror or error}: {error.filename or ''}".rstrip(": ")))
        return stopped("Stopped.", 1)
    except Exception:  # the last resort: any bug is shown and logged, then the run stops as any other does
        traceback.print_exc()
        LOG.exception("a bug")
        fail("That's a bug in tecsun-manager; the details are above.")
        return stopped("Stopped.", 1)


def logs_folder() -> Path:
    """Where the logs go: beside the state file, wherever that is."""
    return STATE_FILE.parent / "logs"


class RunLog(logging.FileHandler):
    """This run's log. Each copied file, cleared sidecar and checked track is a detail (DEBUG): past RUN_LOG_DETAIL
    bytes those stop, and what was shown, asked and changed carries on, so a run over thousands of tracks stays
    small."""

    full = False

    def emit(self, record: logging.LogRecord) -> None:
        try:  # tell() flushes, outside logging's own error handling: a full disk must never stop the run
            past = record.levelno < logging.INFO and self.stream is not None and self.stream.tell() > RUN_LOG_DETAIL
        except (OSError, ValueError):
            return
        if past:
            if not self.full:
                self.full = True
                super().emit(logging.makeLogRecord({
                    "msg": "   … past %s: each file and track isn't logged from here", "args": (human(RUN_LOG_DETAIL),),
                    "levelno": logging.INFO, "levelname": "INFO"}))
            return
        super().emit(record)


def start_log(argv: list[str]) -> None:
    """This run's log: every line shown, every question and its answer, every command run and how it ended, and
    what changed on the card. On unless Settings turned it off. The oldest logs are deleted to keep them all under
    LOGS_SPACE, with room for this one. One that can't be written never stops the run."""
    try:
        logs_folder().mkdir(parents=True, exist_ok=True)
        prune_logs(LOGS_SPACE - RUN_LOG_DETAIL)
        path = logs_folder() / f"{datetime.now().strftime('%Y-%m-%d %H.%M.%S')}.log"  # local time: a name people read
        handler = RunLog(path, encoding="utf-8")
    except OSError:
        return
    handler.setFormatter(logging.Formatter("%(asctime)s  %(message)s", "%H:%M:%S"))
    stop_log()
    LOG.handlers[:] = [handler]
    LOG.setLevel(logging.DEBUG)
    RUN.log = path
    LOG.info("tecsun-manager %s · %s · Python %s · %s · started %s", VERSION, " ".join(argv) or "the menu",
             platform.python_version(), platform.platform(), datetime.now(UTC).isoformat(timespec="seconds"))


def stop_log() -> None:
    """No log from here on. A handler that drops everything takes the file's place, so nothing reopens it, and
    Python never prints a record itself."""
    for handler in LOG.handlers:
        handler.close()
    LOG.handlers[:] = [logging.NullHandler()]
    RUN.log = None


def saved_logs() -> list[Path]:
    """The logs kept, oldest first: their names are dated."""
    try:
        return sorted(logs_folder().glob("*.log"))
    except OSError:
        return []


def prune_logs(room: int) -> None:
    """Delete the oldest logs until the rest take `room` bytes at most."""
    total = 0
    for log in reversed(saved_logs()):
        with suppress(OSError):
            total += log.stat().st_size
            if total > room:
                log.unlink()


def stopped(message: str, code: int) -> int:
    """How every interrupted run ends: writes flushed, and whether the card is still in. Only what the run already
    knows: a stop can come from a wedged card reader, which reading the card could hang on."""
    if RUN.work:
        _line("│", "rail", f"{RUN.work[0]:,} of {plural(RUN.work[1], 'track')} copied before it stopped; the rest "
              "weren't, and no half-copied track is left.", errors)
    os.sync()
    if RUN.card_in_use:
        warn("The card wasn't ejected. Writes are flushed; eject it before you pull it out.")
    # Only a card Clean could take: a locked card, or one with no volume ID, was only read. Both are known
    # already, unlike problem()'s other checks, which read the card.
    for card in (card for card in RUN.used.values() if card.writable and card.uuid):
        warn(f"{esc(card.name)} may not play right until it's cleaned: run {PROG} --clean before it goes back "
             "in the radio.")
    if RUN.log:
        _line("│", "rail", f"[hint]What happened is in {esc(tilde(RUN.log))}[/]", errors)
    outro(message, good=False, to=errors)
    return code


if __name__ == "__main__":
    sys.exit(main())
