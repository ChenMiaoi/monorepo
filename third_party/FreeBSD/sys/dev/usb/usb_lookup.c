/* $FreeBSD$ */
/*-
 * SPDX-License-Identifier: BSD-2-Clause-FreeBSD
 *
 * Copyright (c) 2008 Hans Petter Selasky. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#include "implementation/global_implementation.h"

/*------------------------------------------------------------------------*
 *	usbd_lookup_id_by_info
 *
 * This functions takes an array of "struct usb_device_id" and tries
 * to match the entries with the information in "struct usbd_lookup_info".
 *
 * NOTE: The "sizeof_id" parameter must be a multiple of the
 * usb_device_id structure size. Else the behaviour of this function
 * is undefined.
 *
 * Return values:
 * NULL: No match found.
 * Else: Pointer to matching entry.
 *------------------------------------------------------------------------*/
const struct usb_device_id *
usbd_lookup_id_by_info(const struct usb_device_id *id, usb_size_t sizeof_id,
    const struct usbd_lookup_info *info)
{
	const struct usb_device_id *id_end;

	if (id == NULL) {
		goto done;
	}
	id_end = (const void *)(((const uint8_t *)id) + sizeof_id);

	/*
	 * Keep on matching array entries until we find a match or
	 * until we reach the end of the matching array:
	 */
	for (; id != id_end; id++) {
		if ((id->match_flag_vendor) &&
		    (id->idVendor != info->idVendor)) {
			continue;
		}
		if ((id->match_flag_product) &&
		    (id->idProduct != info->idProduct)) {
			continue;
		}
		if ((id->match_flag_dev_lo) &&
		    (id->bcdDevice_lo > info->bcdDevice)) {
			continue;
		}
		if ((id->match_flag_dev_hi) &&
		    (id->bcdDevice_hi < info->bcdDevice)) {
			continue;
		}
		if ((id->match_flag_dev_class) &&
		    (id->bDeviceClass != info->bDeviceClass)) {
			continue;
		}
		if ((id->match_flag_dev_subclass) &&
		    (id->bDeviceSubClass != info->bDeviceSubClass)) {
			continue;
		}
		if ((id->match_flag_dev_protocol) &&
		    (id->bDeviceProtocol != info->bDeviceProtocol)) {
			continue;
		}
		if ((id->match_flag_int_class) &&
		    (id->bInterfaceClass != info->bInterfaceClass)) {
			continue;
		}
		if ((id->match_flag_int_subclass) &&
		    (id->bInterfaceSubClass != info->bInterfaceSubClass)) {
			continue;
		}
		if ((id->match_flag_int_protocol) &&
		    (id->bInterfaceProtocol != info->bInterfaceProtocol)) {
			continue;
		}
		/* We found a match! */
		return (id);
	}

done:
	return (NULL);
}

/*------------------------------------------------------------------------*
 *	usbd_lookup_id_by_uaa - factored out code
 *
 * Return values:
 *    0: Success
 * Else: Failure
 *------------------------------------------------------------------------*/
int
usbd_lookup_id_by_uaa(const struct usb_device_id *id, usb_size_t sizeof_id,
    struct usb_attach_arg *uaa)
{
	id = usbd_lookup_id_by_info(id, sizeof_id, &uaa->info);
	if (id) {
		/* copy driver info */
		uaa->driver_info = id->driver_info;
		return (0);
	}
	return (ENXIO);
}

#ifndef LITTLE_ENDIAN
#define	LITTLE_ENDIAN 1234
#endif

#ifndef BYTE_ORDER
#define	BYTE_ORDER LITTLE_ENDIAN
#endif

#ifndef BIG_ENDIAN
#define	BIG_ENDIAN 4321
#endif

/*------------------------------------------------------------------------*
 *	Export the USB device ID format we use to userspace tools.
 *------------------------------------------------------------------------*/
#if BYTE_ORDER == BIG_ENDIAN
#define	U16_XOR "8"
#define	U32_XOR "12"
#define	U64_XOR "56"
#define	U8_BITFIELD_XOR "7"
#define	U16_BITFIELD_XOR "15"
#define	U32_BITFIELD_XOR "31"
#define	U64_BITFIELD_XOR "63"
#else
#define	U16_XOR "0"
#define	U32_XOR "0"
#define	U64_XOR "0"
#define	U8_BITFIELD_XOR "0"
#define	U16_BITFIELD_XOR "0"
#define	U32_BITFIELD_XOR "0"
#define	U64_BITFIELD_XOR "0"
#endif

#if USB_HAVE_COMPAT_LINUX
#define	MFL_SIZE "1"
#else
#define	MFL_SIZE "0"
#endif

#if defined(KLD_MODULE) && (USB_HAVE_ID_SECTION != 0)
static const char __section("bus_autoconf_format") __used usb_id_format[] = {

	/* Declare that three different sections use the same format */

	"usb_host_id{256,:}"
	"usb_device_id{256,:}"
	"usb_dual_id{256,:}"

	/* List size of fields in the usb_device_id structure */

#if ULONG_MAX >= 0xFFFFFFFFUL
	"unused{0,8}"
	"unused{0,8}"
	"unused{0,8}"
	"unused{0,8}"
#if ULONG_MAX >= 0xFFFFFFFFFFFFFFFFULL
	"unused{0,8}"
	"unused{0,8}"
	"unused{0,8}"
	"unused{0,8}"
#endif
#else
#error "Please update code."
#endif

	"idVendor[0]{" U16_XOR ",8}"
	"idVendor[1]{" U16_XOR ",8}"
	"idProduct[0]{" U16_XOR ",8}"
	"idProduct[1]{" U16_XOR ",8}"
	"bcdDevice_lo[0]{" U16_XOR ",8}"
	"bcdDevice_lo[1]{" U16_XOR ",8}"
	"bcdDevice_hi[0]{" U16_XOR ",8}"
	"bcdDevice_hi[1]{" U16_XOR ",8}"

	"bDeviceClass{0,8}"
	"bDeviceSubClass{0,8}"
	"bDeviceProtocol{0,8}"
	"bInterfaceClass{0,8}"
	"bInterfaceSubClass{0,8}"
	"bInterfaceProtocol{0,8}"

	"mf_vendor{" U8_BITFIELD_XOR ",1}"
	"mf_product{" U8_BITFIELD_XOR ",1}"
	"mf_dev_lo{" U8_BITFIELD_XOR ",1}"
	"mf_dev_hi{" U8_BITFIELD_XOR ",1}"

	"mf_dev_class{" U8_BITFIELD_XOR ",1}"
	"mf_dev_subclass{" U8_BITFIELD_XOR ",1}"
	"mf_dev_protocol{" U8_BITFIELD_XOR ",1}"
	"mf_int_class{" U8_BITFIELD_XOR ",1}"

	"mf_int_subclass{" U8_BITFIELD_XOR ",1}"
	"mf_int_protocol{" U8_BITFIELD_XOR ",1}"
	"unused{" U8_BITFIELD_XOR ",6}"

	"mfl_vendor{" U16_XOR "," MFL_SIZE "}"
	"mfl_product{" U16_XOR "," MFL_SIZE "}"
	"mfl_dev_lo{" U16_XOR "," MFL_SIZE "}"
	"mfl_dev_hi{" U16_XOR "," MFL_SIZE "}"

	"mfl_dev_class{" U16_XOR "," MFL_SIZE "}"
	"mfl_dev_subclass{" U16_XOR "," MFL_SIZE "}"
	"mfl_dev_protocol{" U16_XOR "," MFL_SIZE "}"
	"mfl_int_class{" U16_XOR "," MFL_SIZE "}"

	"mfl_int_subclass{" U16_XOR "," MFL_SIZE "}"
	"mfl_int_protocol{" U16_XOR "," MFL_SIZE "}"
	"unused{" U16_XOR "," MFL_SIZE "}"
	"unused{" U16_XOR "," MFL_SIZE "}"

	"unused{" U16_XOR "," MFL_SIZE "}"
	"unused{" U16_XOR "," MFL_SIZE "}"
	"unused{" U16_XOR "," MFL_SIZE "}"
	"unused{" U16_XOR "," MFL_SIZE "}"
};
#endif
