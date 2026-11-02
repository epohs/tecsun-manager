# tecsun-manager manual

[Synopsis](#synopsis) · [Requirements](#requirements) · [Linux](#linux) · [Options](#options) · [Getting around](#getting-around) · [Tasks](#tasks) · [Settings](#settings) · [Files](#files) · [Safety](#safety) · [Exit status](#exit-status) · [Uninstall](#uninstall)


## Synopsis

```
tecsun-manager
tecsun-manager --add | --arrange | --clean | --backup | --restore | --check | --stats | --playlist
tecsun-manager --help | --version
```

With no options, the script opens a menu and asks questions as it goes. A task option skips the menu and runs just that task. Either way it's interactive, so it needs a terminal. It takes no paths: each task asks for its card or folder.

Albums are folders at the top of the card, named `NN - Artist - Album`. Tracks are the audio files directly inside each album folder. The number sets the order the radio plays them in. The radio actually plays them in the order they sit on the card, so after every change the script runs fatsort to put the card in number order. Numbers sort naturally and case is ignored, so 2 comes before 10.


## Requirements

- macOS or Linux, and [uv](https://docs.astral.sh/uv/). uv fetches Python 3.14 or newer and the packages the script needs on the first run.
- [fatsort](https://fatsort.sourceforge.io) puts the card in play order. Without it, nothing gets sorted.
- [par2](https://github.com/Parchive/par2cmdline) adds repair data to backups. Optional.
- flac checks FLAC files for damage, and ffmpeg checks every format. Optional, but finding damaged tracks needs one of them.

When it starts, the script tells you if fatsort or par2 is missing, or if neither flac nor ffmpeg is installed.

Some steps need your admin password: fatsort, clearing Spotlight's folder off the card, and reading the card's file table. Clearing Spotlight's folder doesn't ask when your terminal has Full Disk Access. sudo asks for the password in the terminal, so it never reaches the script or its logs.


## Linux

The same script runs on Linux with `lsblk`, and ideally `udisks2`. Without udisks2, unmounting the card takes your password, and an unmounted card can't be mounted again, so the script ejects it instead of offering **Keep it mounted**. exFAT cards need fatsort 1.7 or newer. Debian 13 and Ubuntu ship 1.6, which can't read exFAT, so build 1.7 from [fatsort.sourceforge.io](https://fatsort.sourceforge.io). FAT32 cards are fine with 1.6. Linux can't check for [tracks stored in pieces](#tracks-stored-in-pieces).


## Options

Use one option at a time. They can't be shortened, so `--clean` works but `--cl` doesn't.

| Option | Runs |
|---|---|
| `--add` | [Add albums](#add-albums) |
| `--arrange` | [Arrange albums](#arrange-albums) |
| `--clean` | [Clean the card](#clean-the-card) |
| `--backup` | [Back up](#back-up) |
| `--restore` | [Restore](#restore) |
| `--check` | [Check](#check) |
| `--stats` | [Stats](#stats) |
| `--playlist` | [Generate playlist](#generate-playlist) |
| `-h`, `--help` | Lists the tasks and options. If it's anywhere on the line, help is all that runs |
| `-V`, `--version` | Prints the version |

A mistyped option gets a suggestion, like "Did you mean --check?".


## Getting around

| Key | Does |
|---|---|
| ↑ ↓ and Enter | Move and pick |
| Type | Filter a long list. What you've typed shows under the question |
| Backspace | Edit the filter |
| Tab | Complete a typed path |
| y, n | Answer a yes/no question. Enter takes the default, the capital letter in (Y/n) |
| Esc | Go back: **Back** in a list, No on most yes/no questions, Quit at the menu. In a filtered list it clears the filter first. Where No would go ahead, like skipping a backup before a delete, Esc goes back instead |
| Ctrl-C | Stop. If albums are being sorted, renamed or deleted, or the card is being reformatted, the script waits until that's done |

- Lists show the items first, like albums or cards. Below a line are the actions, in their own color: → looks elsewhere, ← goes back, ↻ rescans.
- The line above each question says what's being done to what, like "Moving 03 - Morning Edition". Once you've confirmed the card, its name, album count and free space sit at the right of that line.
- Before most changes, the script asks if you want to go ahead. The first answer spells out the change, like "Copy 12 tracks, then clean and sort", and the second is **Back**. When the change deletes albums, or drops files from a kept-current backup, the highlight starts on **Back**, so pressing Enter right away cancels.
- **Replace everything** asks you to type the card's name before it erases the card, so you can't erase the wrong one.
- After a change, a box titled with the card's name lists what changed and whether the play order checked out.
- After a task, the menu comes back. Later tasks reuse the confirmed card until it's ejected, or a drive is plugged in or removed.
- Each time the menu comes back after a task finishes, and each time Help opens, a line with the time marks the spot, so the newest is easy to find when you scroll back. To start each task on a clean screen instead, turn off [Keep scrollback](#keep-scrollback).

### The menu

| Group | Tasks |
|---|---|
| On the card | Add albums, Arrange albums, Clean the card |
| Backups | Back up, Restore |
| Info | Check, Stats, Generate playlist |

Below those are Help, with a page for each task, then Settings and Quit. If the script has changed a plugged-in card since its last backup, a reminder shows above the menu. Changes made in Finder don't count, since it can't know about them.

### Picking the card

You pick the card from a list of removable and external drives. The computer's own drives never show up. With one card plugged in, the script goes straight to "Is this the right card?" and shows what's on it. If no card is found, it offers to rescan.

Two tasks can use a folder instead of a card: Back up, and **Find damaged tracks** under Check. They're read-only, so they skip "Is this the right card?". Instead they ask what to back up or scan, and list the cards and **A folder** together. When one of them finishes with a card, it offers to clean it, since macOS leaves hidden files on any card that's plugged in. The question names the card, like "Clean, re-sort and eject RADIO now?" A locked card, or one with no volume ID, isn't offered this, since the script can't change it.

Some cards are greyed out and can't be picked: a locked card, a card that isn't FAT or exFAT, a card with no volume ID (the script checks that ID before every write), an XTEINK e-reader's card (it has a `.crosspoint` folder, which cleaning would delete), and a card mounted on a system folder instead of its own. Tasks that only read, like Stats and Back up, can still use a locked card or one with no volume ID.

### Keeping the card mounted

From the menu, every task that cleans the card ends by asking **Eject** or **Keep it mounted**. On Linux, that needs udisks2 (see [Linux](#linux)). A kept card is sorted, then mounted again for the next task.

While a card is still mounted, the menu shows a yellow **Clean and eject** item for it. When you quit, the script lists any card you used that's still mounted, says what could trip the radio up, and offers to clean and eject it. A task run from the command line asks the same at the end. A run that's stopped (Ctrl-C, a `kill`, a crash) names each card that still needs cleaning.


## Tasks

### Add albums

`--add` · Copies new albums from a folder onto the card, each at the place its number says, and renumbers the albums after it.

- Put just the new albums in a folder, numbered where they go, like `05 - Artist - Album`.
- Unless the card is empty, **Add how?** comes first. **Add albums** keeps what's on the card. **Replace everything** erases the card, then copies the folder's albums under their own names. It asks you to type the card's name, warns if the card would end up with fewer albums, and keeps the card's format.
- If an album on the card already has that number, it asks where the new one goes.
- A track already on the card with the same name and size is skipped. One whose size changed is replaced.
- On a FAT32 card, it asks for your password before copying, so each track can land in one piece. See [Tracks stored in pieces](#tracks-stored-in-pieces).
- **Add albums** matches albums by title, so if two albums share a title, in the folder or on the card, it stops and names them.
- Afterwards it offers a backup, then cleans, sorts and ejects the card.

### Arrange albums

`--arrange` · Moves, renames or deletes albums and renumbers the rest. Only folder names change, so it takes seconds.

- **Move an album** puts it somewhere else. The rest renumber.
- **Rename an album** changes its name. The number stays.
- **Delete an album** removes it from the card. The rest renumber. First it says when the card was last backed up and offers a fresh backup.
- **Fix numbering** shows up when the numbers have gaps, repeats or uneven zero-padding, or an album has no number. It renumbers without changing the order.
- When you're done, **Apply and clean** makes all your changes, offers a backup unless you deleted albums, then cleans, sorts and ejects. Nothing on the card changes until you pick it.

**Cancel** asks before it throws your changes away.

### Clean the card

`--clean` · Run this whenever the card has been plugged into a Mac, before it goes back in the radio.

- Removes every hidden item at the top of the card (any name that starts with a dot, like `.fseventsd` and `.Spotlight-V100`), and `._`, `.DS_Store` and `.apdisk` files and leftover partial copies anywhere. The radio can mistake them for albums. Don't keep files of your own on the card under names that start with a dot.
- Finds tracks stored in pieces and, on a FAT32 card, offers to rewrite each one whole.
- Sorts the card with fatsort, reads the order back to check it, and ejects.

#### Tracks stored in pieces

The radio skips a track that's stored in pieces scattered across the card, even though the file plays fine on a computer.

These split tracks come from gaps. Deleting albums, and cleaning away the hidden files macOS adds, leaves small empty spaces all over the card. macOS fills the earliest spaces first, so a big track copied later can be split across many of them.

Before any task sorts the card, the script checks for split tracks. On a FAT32 card, with your admin password, it offers to rewrite each in one piece. It copies the track into an unbroken stretch of free space, checks that the copy matches the original and is whole, and only then swaps it in. Names and play order don't change. To keep the copy out of the small gaps, the script fills them with a placeholder file first, and deletes it once the copy is done. On a FAT32 card, Add does the same when it copies new tracks, so they start out whole.

- Finding every split track means reading the card's file table, its record of where each piece of every file sits. That takes your password and only works on FAT32 cards.
- Without the password, or on an exFAT card, a quick check finds only some split tracks, and they can't be rewritten. Check says when the quick check might have missed some.
- Rewriting needs fatsort, which puts each rewritten track back in its place in the play order.
- When no stretch of free space is big enough for a track, the script says so.
- Linux can't check for this.

When a split track can't be rewritten, rebuild the card: back up the card, restore the backup, then use **Add → Replace everything** from the restored folder. Copying onto an erased card lays every track down in one piece.

### Back up

`--backup` · Packs the card, or a folder of albums, into one archive with checksums. It checks the audio first, reads the archive back from the drive to check every file, then adds repair data.

**Into?** offers a new dated backup, or a kept-current one.

A dated backup gets its own folder and is never changed, except when Restore repairs damage from its repair data, which puts back the original. Its files are named after the card or folder you back up:

```
tecsun-backups/2026-10-08/
  TECSUN 990X.tar.zst           the albums: a standard tar, zstd-compressed
  TECSUN 990X.tar.zst.sha256    checksums; shasum -a 256 -c reads it too
  TECSUN 990X.tar.zst.par2      repair data, plus .vol files; needs par2
```

A kept-current backup is the one you update after each change, instead of piling up dated ones. Pick **Start a kept-current backup** the first time. After that, **Update** is the default.

```
tecsun-backups/TECSUN 990X (kept current)/
  TECSUN 990X.tar.zst           the same three files as a dated backup
  TECSUN 990X.tar.zst.sha256
  TECSUN 990X.tar.zst.par2
  .source.json                  which card or folder it's of, and when it was last updated
```

- It's the only kind of backup the script updates.
- A compressed archive can't be patched, so each update re-reads the whole card. It takes about as long as a new backup and needs room for two copies until the new one checks out.
- Before updating, it lists what changes: albums added, dropped, renumbered or renamed, and files added or dropped. When anything would be dropped, Enter means No.
- A file that kept its name but changed its contents is most likely damage, so it names those and asks before the new copy moves in.
- The new copy is built beside the old one and only moves in once it reads back cleanly. A stopped update leaves the old copy whole.

Add and Arrange offer a backup when they finish, if they changed anything: an update of the card's kept-current backup when it has one, otherwise a new dated one. When Arrange deletes albums, the offer comes before the delete instead, and is always a new dated backup.

**Save the backup where?** starts at the folder in use. Type another to change it, and it's remembered. On macOS, a folder on a drive that isn't plugged in is refused rather than made on your computer. A folder inside what you're backing up is refused, and so is a FAT drive when the backup would pass 4 GB.

### Restore

`--restore` · Unpacks a backup and checks every file against its checksum. The files land in a folder named after the card or folder that was backed up, inside the folder you pick.

- A damaged backup with repair data is repaired first (needs par2).
- It unpacks into a hidden folder first. Files already there are replaced only after everything checks out. If anything fails its check, what was unpacked moves to a separate `(unverified <date>)` folder beside it instead.
- A backup without its checksum file can only be checked for unpacking cleanly, and it says so.
- It never restores straight onto a card. To put a backup back on the card, restore it, then use **Add → Replace everything** from the restored folder.
- It also reads `.tar.xz`, `.tar.bz2` and `.tar.gz` backups.

### Check

`--check` · **Check what?** offers three things:

- **Verify a backup**: tests every file inside it against its checksums, without unpacking, and checks its repair data.
- **Find damaged tracks**: decodes every track on the card, one album, or a folder, and names any that don't play cleanly.
- **Read the card's play order**: reads the order straight off the card and compares it with the numbers. On macOS the card stays mounted while it reads, and it also names hidden files and tracks stored in pieces. If anything's wrong, it offers to clean, sort and eject. On Linux it offers to sort.

### Stats

`--stats` · Shows the card at a glance: albums and tracks, how full it is, its formats and largest albums with a bar for each, and when it was last backed up. Nothing is decoded, so it's quick.

### Generate playlist

`--playlist` · Writes the card's albums as a list to keep: each one's number, artist and album, in play order, split from the folder names. Nothing on the card changes. See the [examples](examples/).

| File | For |
|---|---|
| `tecsun-playlist.epub` | An e-reader. Page one is the album list, then each album gets a chapter with its tracks. Its cover shows the first albums. Made for the XTEINK X4 |
| `tecsun-playlist.pdf` | Printing. A card that folds up and lives in the radio's case |
| `tecsun-playlist.html` | A browser. One file, light or dark with your system |

- Each run replaces the last set. At **Save as**, **Another name…** writes a new set and keeps the old one.
- **On the X4:** copy the EPUB onto its SD card. The X4 doesn't notice a book replaced under the same name, and keeps showing the old one's cover and chapters, so give a newer list another name.
- **On paper:** print the PDF at 100% (not fit to page) on US Letter. Cut the sheet down the middle, then fold a half across its middle into a 5.5 × 4.25 in card. That's about 45 albums a card. When the list fits on one card, the other half is a spare.


## Settings

The menu's Settings has two settings, both on by default.

### Debug logging

Each run writes a log of what it showed, what it asked, what you answered, every command it ran, and every change to the card. When a run stops or crashes, its last lines name the log. Your password never ends up in it.

- Each run writes its own log file. When the script starts, it deletes the oldest log files, a whole run at a time, so that all the logs together stay around 5 MB.
- If one run's log grows past 1 MB, as when checking thousands of tracks, it stops noting each file one by one. It still notes everything else: what the script showed, what you answered, and what changed.
- Turning logging off stops the current log right away and offers to delete the old ones.

### Keep scrollback

With Keep scrollback on, the default, everything the script shows stays in the terminal, so you can scroll back through the whole session. Each time the menu comes back after a task finishes, and each time Help opens, a line with the time marks the spot. The time matches the log's.

With Keep scrollback off, each pick from the menu clears the terminal window and its scrollback, so only the task you picked is there. Its result stays on screen until your next pick, and you can still scroll up through a long page. Quit doesn't clear, so the last result stays after the script ends.

- The first clear also removes whatever was in the terminal window before you started the script.
- A task run from the command line, like `--add`, always keeps its output.


## Files

| Where | What |
|---|---|
| `~/.config/tecsun-manager/state.json` | What the script remembers: the last folders, card and backup, when each card's albums last changed and were last backed up, your backups folder, and your [Settings](#settings). Delete it to forget them, and both settings go back on. Uses `$XDG_CONFIG_HOME` instead of `~/.config` when that's set |
| `~/.config/tecsun-manager/logs/` | A log of each run, beside `state.json`. See [Settings](#settings) |
| `tecsun-backups/` | Where backups go: next to the script, unless you pick another folder |
| `~/Desktop/Tecsun Restored/` | Where [Restore](#restore) suggests unpacking, until you pick another folder |
| `tecsun-playlist.epub`, `.pdf`, `.html` | Where [Generate playlist](#generate-playlist) saves its files: next to the script |

A few rarely changed settings sit at the top of `tecsun-manager.py`: the audio file types, how much repair data backups get, the compression level, where backups and playlists go, and the printed playlist's type size.


## Safety

- Before a task changes the card, the script shows what's on it and asks if it's the right one. It skips that question only when it already knows which card you mean, and names the card instead. That happens when you confirmed the card earlier in the run, when you pick the yellow **Clean and eject** item, and when it offers to clean the card after Back up, after **Find damaged tracks**, or at Quit.
- Before every write, the script checks the card's ID to make sure the same card is still there. A swapped card stops the run.
- In a filtered list, Enter does nothing until the filter matches, so a typo can't pick the first album.
- Tracks copy under a temporary name and are flushed to the card before they get their real name, so a cut-short copy never leaves half a track.
- If you press Ctrl-C, or the run gets a `kill`, while fatsort, a batch of renames or deletes, or a reformat is changing the card, the script waits for that to finish first. fatsort itself is never interrupted.
- A rewritten track replaces the original only after the copy reads back the same and in one piece. A copy left by a stopped rewrite is never cleaned away while it might be the only one.
- Arrange's **Delete** only ever removes album folders. Clean removes only hidden items, and only **Replace everything** erases the whole card.
- The folder you copy from is only ever read.


## Exit status

| Code | Means |
|---|---|
| 0 | Everything went well |
| 1 | Something failed, or Check found a damaged backup or a damaged track, or left the card out of play order, or couldn't read the order |
| 2 | An option it doesn't know, two options at once, a path, no terminal, or a system other than macOS or Linux |
| 130 | Stopped with Ctrl-C, or Ctrl-D in an empty field |
| 128 + N | Stopped by signal N, like a `kill` or a closed terminal |

Warnings and errors go to stderr.


## Uninstall

```bash
rm ~/.local/bin/tecsun-manager                            # the launcher, if you made one
rm -r "${XDG_CONFIG_HOME:-$HOME/.config}/tecsun-manager"  # what it remembers, and the logs
uv cache prune                                            # the script's cached environment
```

uv still keeps the packages it downloaded. `uv cache clean` empties its cache, and `uv python uninstall <version>` removes the Python it fetched, if it fetched one. `uv python list --only-installed` shows which version that is. Do either only if nothing else of yours uses uv.

Then delete the folder. Move `tecsun-backups/` somewhere safe first: your backups are in it.
