#ifndef STATIC

#include <stdio.h>
#include <stdlib.h> //for abort
#include <gc.h>

#include "crc.h"
#include "fun.h"
#include "lst.h"
#include "capp.h"
#include "app.h"
#include "ty.h"

#if defined(CAST) || defined(ALT)
value fun_wrapped_call_funcM(value cls, value arg) {
	// closureから関数と、wrapしている情報を取り出す
    fun *inner_f = (fun*)((fun*)cls)->env[0];
	#ifdef CAST
	ty *t1 = (ty*)((fun*)cls)->env[1];
	ty *t2 = (ty*)((fun*)cls)->env[2];
	uint32_t rid = (uint32_t)(uintptr_t)((fun*)cls)->env[3];
	uint8_t polarity = (uint8_t)(uintptr_t)((fun*)cls)->env[4];
	#else // CAST
    crc *c = (crc*)((fun*)cls)->env[1];
	#endif // CAST

	value inner_f_val = (value)inner_f;

	// Coercion / Cast 適用し、return
	#ifdef CAST
	ty *t11 = t1->tydat.tyfun.left;
	ty *t12 = t1->tydat.tyfun.right;
	ty *t21 = t2->tydat.tyfun.left;
	ty *t22 = t2->tydat.tyfun.right;
	uint8_t neg_polarity = polarity ^ 1;
	value _arg = cast(arg, t21, t11, rid, neg_polarity);
	value ret = inner_f->funcM(inner_f_val, _arg);
	return cast(ret, t12, t22, rid, polarity);
	#else // CAST
    crc *c1 = c->crcdat.fun_crc.c1;
    crc *c2 = c->crcdat.fun_crc.c2;
    value _arg = coerce(arg, c1);
	if (c2 == &crc_id) {
		return inner_f->funcM(inner_f_val, _arg);
	} else {
		value c2_val = (value)c2;
    	return inner_f->funcD(inner_f_val, _arg, c2_val);
	}
	#endif // CAST
}
#endif // CAST || ALT

#ifndef CAST
value fun_wrapped_call_funcD(value cls, value arg1, value arg2) {
	// closureから関数と、wrapしている情報を取り出す
    fun *inner_f = (fun*)((fun*)cls)->env[0];
    crc *c = (crc*)((fun*)cls)->env[1];

    value inner_f_val = (value)inner_f;

	// Coercion 適用し、return
    crc *c1 = c->crcdat.fun_crc.c1;
    crc *c2 = c->crcdat.fun_crc.c2;
    crc *_arg2_crc = compose(c2, (crc*)arg2);
    value _arg1 = coerce(arg1, c1);
	#ifdef ALT
	if (_arg2_crc == &crc_id) {
		return inner_f->funcM(inner_f_val, _arg1);
	} else {
		value _arg2 = (value)_arg2_crc;
		return inner_f->funcD(inner_f_val, _arg1, _arg2);
	}
	#else
	value _arg2 = (value)_arg2_crc;
	return inner_f->funcD(inner_f_val, _arg1, _arg2);
	#endif
}
#endif // not CAST

#endif // not STATIC