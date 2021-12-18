/* Handle wine shared libraries for GDB, the GNU Debugger.

   Copyright (C) 1990-2021 Free Software Foundation, Inc.

   This file is part of GDB.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

#include "defs.h"

#include "symtab.h"
#include "charset.h"
#include "bfd.h"
#include "symfile.h"
#include "objfiles.h"
#include "gdbcore.h"
#include "target.h"
#include "inferior.h"
#include "infrun.h"
#include "regcache.h"
#include "gdbthread.h"
#include "observable.h"
#include "coff/internal.h"
#include "libcoff.h"

#include "extract-store-integer.h"
#include "solist.h"
#include "solib.h"
#include "solib-svr4.h" // for lm_info_svr4
#include "solib-wine.h"

#include "solib-winabi.c"

/* Per-architecture data key.  */
static const registry<gdbarch>::key<struct solib_wine_ops> solib_wine_data;

struct solib_wine_ops
{
  const solib_ops *host_so_ops = nullptr;
  bool (*get_current_tib_addr)(CORE_ADDR*) = nullptr;
};

/* Per pspace wine specific data.  */
struct wine_info
{
  solib *host_so_list = nullptr;
};

/* Per-program-space data key.  */
static const registry<program_space>::key<wine_info> solib_wine_pspace_data;

/* Get the wine data for program space PSPACE.  If none is found yet, add it now.
   This function always returns a valid object.  */

static wine_info *
get_wine_info (program_space *pspace)
{
  struct wine_info *info = solib_wine_pspace_data.get (pspace);

  if (info == NULL)
    info = solib_wine_pspace_data.emplace (pspace);

  return info;
}

/* Return a default for the architecture-specific operations.  */

static solib_wine_ops *
get_ops (gdbarch *gdbarch)
{
  solib_wine_ops *ops = solib_wine_data.get (gdbarch);
  if (ops == nullptr)
    ops = solib_wine_data.emplace (gdbarch);
  return ops;
}

static void
wine_relocate_section_addresses (solib &so, target_section *sec)
{
  gdbarch *gdbarch = current_inferior ()->arch();
  solib_wine_ops *ops = get_ops (gdbarch);

  if (so.wine_so_ops == &wine_so_ops)
  {
    bfd *abfd = sec->the_bfd_section->owner;
    CORE_ADDR ImageBase = pe_data (abfd)->pe_opthdr.ImageBase;

    const lm_info_svr4 *li = gdb::checked_static_cast<const lm_info_svr4 *> (so.lm_info.get());
    sec->addr += li->l_addr - ImageBase;
    sec->endaddr += li->l_addr - ImageBase;
  } else {
    ops->host_so_ops->relocate_section_addresses (so, sec);
  }
}

static void
wine_free_objfile_observer (struct objfile *objfile)
{
  static int once;
  if (!once) {
    warning (_("todo: %s\n"), __FUNCTION__);
    once++;
  }
}

static void
wine_clear_so(const solib &so)
{
  gdbarch *gdbarch = current_inferior ()->arch();
  solib_wine_ops *ops = get_ops (gdbarch);

  if (so.wine_so_ops == &wine_so_ops)
  {
  } else {
    ops->host_so_ops->clear_so (so);
  }
}

static void
wine_clear_solib (program_space *pspace)
{
  gdbarch *gdbarch = current_inferior ()->arch();
  solib_wine_ops *ops = get_ops (gdbarch);

  if (ops->host_so_ops)
    ops->host_so_ops->clear_solib (pspace);
}

static void
wine_solib_create_inferior_hook (int from_tty)
{
  gdbarch *gdbarch = current_inferior ()->arch();
  solib_wine_ops *ops = get_ops (gdbarch);

  ops->host_so_ops->solib_create_inferior_hook (from_tty);
}

/*
    MIT License

    Copyright (c) Microsoft Corporation.

    Permission is hereby granted, free of charge, to any person obtaining a copy
    of this software and associated documentation files (the "Software"), to deal
    in the Software without restriction, including without limitation the rights
    to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
    copies of the Software, and to permit persons to whom the Software is
    furnished to do so, subject to the following conditions:

    The above copyright notice and this permission notice shall be included in all
    copies or substantial portions of the Software.

    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
    IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
    FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
    AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
    LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
    OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
    SOFTWARE
  */

template <typename ptr_t> struct LIST_ENTRY {
   ptr_t *Flink;
   ptr_t *Blink;
};

template <typename ptr_t> struct UNICODE_STRING
{
  uint16_t Length;
  uint16_t MaximumLength;
  ptr_t Buffer;
};

template <typename ptr_t> struct LDR_DATA_TABLE_ENTRY {
  LIST_ENTRY<ptr_t> InLoadOrderLinks;
  LIST_ENTRY<ptr_t> InMemoryOrderLinks;
  LIST_ENTRY<ptr_t> InInitializationOrderLinks;
  ptr_t DllBase;
  ptr_t EntryPoint;
  ptr_t SizeOfImage;
  UNICODE_STRING<ptr_t> FullDllName;
};

static void wine_read_so_list(CORE_ADDR list_head, bool iswin64, enum bfd_endian byte_order, owning_intrusive_list<solib> &sos)
{
  CORE_ADDR next_entry = 0;
  for (CORE_ADDR entry = list_head; next_entry != list_head; entry = next_entry)
  {
    auto &newobj = sos.emplace_back ();
    if (iswin64)
    {
      LDR_DATA_TABLE_ENTRY<uint64_t> ldr;
      if (target_read_memory (entry, (gdb_byte*)&ldr, sizeof(ldr)) != 0) {
        warning (_("Error reading shared library list entry at %s"),
          paddress (current_inferior ()->arch(), entry));
        break;
      }

      std::vector<gdb_byte> full_name(ldr.FullDllName.Length);
      if (target_read_memory (ldr.FullDllName.Buffer, full_name.data(), full_name.size()) != 0) {
        warning (_("Error reading shared library full name at %s"),
          paddress (current_inferior ()->arch(), ldr.FullDllName.Buffer));
        break;
      }

      newobj.lm_info = std::make_unique<lm_info_svr4>();
      lm_info_svr4 *li = gdb::checked_static_cast<lm_info_svr4 *> (newobj.lm_info.get());
      li->l_addr = ldr.DllBase;
      li->l_addr_p = true;

      auto_obstack converted_name;
      convert_between_encodings ("UTF-16", host_charset(),
              full_name.data(),
              full_name.size(),sizeof(uint16_t),&converted_name,
              translit_none);
      obstack_1grow (&converted_name, '\0');
      newobj.so_original_name = (char*)obstack_base (&converted_name);

      newobj.so_name = (char*)obstack_base (&converted_name);
      // TODO: Path translation, for now just rewrite path separators
      char *path = newobj.so_name.data();
      while (*path) {
        if (*path == '\\')
          *path = '/';
        path++;
      }

      next_entry = extract_unsigned_integer((gdb_byte*)&ldr.InLoadOrderLinks.Flink, 8, byte_order);
    }
    else
    {
      LDR_DATA_TABLE_ENTRY<uint32_t> ldr;
      if (target_read_memory (entry, (gdb_byte*)&ldr, sizeof(ldr)) != 0)
        warning (_("Error reading shared library list entry at %s"),
          paddress (current_inferior ()->arch(), entry));
      error("TODO");
    }
    newobj.wine_so_ops = &wine_so_ops;
  }
}

static owning_intrusive_list<solib>
wine_current_sos ()
{
  wine_info *info = get_wine_info (current_program_space);
  (void)info;

  gdbarch *gdbarch = current_inferior ()->arch();
  enum bfd_endian byte_order = gdbarch_byte_order (gdbarch);
  solib_wine_ops *ops = get_ops (gdbarch);

  // Load host sos
  owning_intrusive_list<solib> sos;
  if (ops->host_so_ops)
    sos = ops->host_so_ops->current_sos ();

  bool win64 = gdbarch_ptr_bit (gdbarch) == 64;

  // Load wine sos
  CORE_ADDR tib;
  if (!ops->get_current_tib_addr (&tib)) {
    warning (_("Error reading TIB"));
    return sos;
  }

  CORE_ADDR peb;
  if (!winabi_target_get_peb(tib, win64, byte_order, &peb)) {
    warning (_("Error reading PEB addr from TIB at address %s"), paddress (current_inferior ()->arch(), tib));
    return sos;
  }

  CORE_ADDR lm;
  if (!winabi_ldr_in_load_order_list(peb, win64, byte_order, &lm)) {
    warning (_("Error reading shared library list from PEB at address %s"), paddress (current_inferior ()->arch(), peb));
    return sos;
  }

  wine_read_so_list (lm, win64, byte_order, sos);

  return sos;
}

static int
wine_in_dynsym_resolve_code (CORE_ADDR pc)
{
  gdbarch *gdbarch = current_inferior ()->arch();
  solib_wine_ops *ops = get_ops (gdbarch);

  return ops->host_so_ops->in_dynsym_resolve_code (pc);
}

static int
wine_same (const solib &gdb, const solib &inferior)
{
  gdbarch *gdbarch = current_inferior ()->arch();
  solib_wine_ops *ops = get_ops (gdbarch);

  if (gdb.wine_so_ops == &wine_so_ops || inferior.wine_so_ops == &wine_so_ops)
  {
    return 1;
  } else {
    return ops->host_so_ops->same (gdb, inferior);
  }
}

static int
wine_keep_data_in_core (CORE_ADDR vaddr, unsigned long size)
{
  gdbarch *gdbarch = current_inferior ()->arch();
  solib_wine_ops *ops = get_ops (gdbarch);

  return ops->host_so_ops->keep_data_in_core (vaddr, size);
}

static void
wine_update_breakpoints ()
{
  gdbarch *gdbarch = current_inferior ()->arch();
  solib_wine_ops *ops = get_ops (gdbarch);

  ops->host_so_ops->update_breakpoints ();
}

static void
wine_handle_event (void)
{
  gdbarch *gdbarch = current_inferior ()->arch();
  solib_wine_ops *ops = get_ops (gdbarch);

  ops->host_so_ops->handle_event ();
}

static std::optional<CORE_ADDR>
wine_find_solib_addr (solib &so)
{
  if (so.wine_so_ops == &wine_so_ops) {
    auto *li = gdb::checked_static_cast<lm_info_svr4 *> (so.lm_info.get ());
    return li->l_addr;
  }
  return {};
}

void set_solib_wine (struct gdbarch *gdbarch, bool (*get_current_tib_addr)(CORE_ADDR*)) {
  solib_wine_ops *ops = get_ops (gdbarch);
  ops->host_so_ops = gdbarch_so_ops (gdbarch);
  ops->get_current_tib_addr = get_current_tib_addr;
  set_gdbarch_so_ops (gdbarch, &wine_so_ops);
}

static int
wine_open_symbol_file_object (int from_tty)
{
  gdbarch *gdbarch = current_inferior ()->arch();
  solib_wine_ops *ops = get_ops (gdbarch);

  return ops->host_so_ops->open_symbol_file_object (from_tty);
}

const struct solib_ops wine_so_ops =
{
  wine_relocate_section_addresses,
  wine_clear_so,
  wine_clear_solib,
  wine_solib_create_inferior_hook,
  wine_current_sos,
  wine_open_symbol_file_object,
  wine_in_dynsym_resolve_code,
  solib_bfd_open,
  wine_same,
  wine_keep_data_in_core,
  wine_update_breakpoints,
  wine_handle_event,
  wine_find_solib_addr,
};

void _initialize_wine_solib ();
void
_initialize_wine_solib ()
{
  gdb::observers::free_objfile.attach (wine_free_objfile_observer,
				       "solib-wine");
}
