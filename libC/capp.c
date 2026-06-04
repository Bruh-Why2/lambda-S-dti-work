#ifndef STATIC

#include <stdio.h>
#include <stdlib.h> //for abort
#include <gc.h>

#include "crc.h"
#include "fun.h"
#include "lst.h"
#include "tpl.h"
#include "app.h"
#include "ty.h"

#include "capp.h"

#ifdef PROFILE
static inline void update_longest(int new) {
	if (new > current_longest) {
		current_longest = new;
	}
	return;
}
#endif

static inline uint8_t tag_of(value v) {
	return (v & 0b111);
}

static inline value tag_value(value v, uint8_t t) {
	#ifdef PROFILE
	update_longest(1);
	#endif
	switch(t) {
		case G_INT:
		case G_BOOL:
		case G_UNIT:
			return (value)(v << 3 | t);
		case G_AR:
		case G_LI:
		case G_TP:
			return (value)(v | t);
		default: {
			printf("%d is not ground_ty", t);
			exit(1);
		}
	}
}

static inline value untag_value(value v, uint8_t t) {
	switch(t) {
		case G_INT:
		case G_BOOL:
		case G_UNIT:
			return (value)(v >> 3);
		case G_AR:
		case G_LI:
		case G_TP:
			return (value)(v & ~0b111);
		default: {
			printf("%d is not ground_ty", t);
			exit(1);
		}
	}
}

static inline uint16_t arity_of(value v) {
	switch(tag_of(v)) {
		case G_TP: {
			#ifdef EAGER
			return ((tpl*)untag_value(v, G_TP))->hdr.arity;
			#else
			return ((tpl*)untag_value(v, G_TP))->arity;
			#endif
		}
		default: return 0;
	}
}

#ifdef CAST
#include "ty.h"

int ty_equal (ty *t1, ty *t2) {
	if (t1 == t2) return 1;
	enum tykind tk1 = t1->tykind;
	enum tykind tk2 = t2->tykind;
	if (t1->tykind == t2->tykind) {
		switch (t1->tykind) {
			case DYN:
			case BASE_INT:
			case BASE_BOOL:
			case BASE_UNIT:
				return 1;
			case TYFUN:
				return ty_equal(t1->tydat.tyfun.left, t2->tydat.tyfun.left) && ty_equal(t1->tydat.tyfun.right, t2->tydat.tyfun.right);
			case TYLIST:
				return ty_equal(t1->tydat.tylist, t2->tydat.tylist);
			case TYTUPLE: {
				if (t1->tydat.tytuple.arity != t2->tydat.tytuple.arity) return 0;
				for (int i = 0; i < t1->tydat.tytuple.arity; i++) {
					if (!ty_equal(t1->tydat.tytuple.tys[i], t2->tydat.tytuple.tys[i])) return 0;
				}
				return 1;
			}
			case TYVAR:
				return t1 == t2;
		} 
	} else {
		return 0;
	}
}

ty *get_dyn_tuple_ty(uint16_t arity) {
	ty *retty = (ty*)GC_MALLOC(sizeof(ty));
	retty->tykind = TYTUPLE;
	retty->tydat.tytuple.arity = arity;
	retty->tydat.tytuple.tys = (ty**)GC_MALLOC(sizeof(ty*) * arity);
	for (int i = 0; i < arity; i++) {
		retty->tydat.tytuple.tys[i] = &tydyn;
	}
	return retty;
}

value cast(value x, ty *t1, ty *t2, uint32_t rid, uint8_t polarity) {			// input = x:t1=>t2
	#ifdef PROFILE
	current_cast++;
	#endif
	// when t1 and t2 are same // R_ID (x:U=>U -> x)
	if (t1 == t2) return x;
	if (ty_equal(t1, t2)) return x;

	enum tykind tk1 = t1->tykind;
	enum tykind tk2 = t2->tykind;
	
	switch(tk1) {
		case BASE_INT: {			// when t1 is ground and t2 is ?
			switch(tk2) {
				case DYN: return tag_value(x, G_INT); // define x:G=>? as dynamic type value
				default: break;
			}
			break;
		}
		case BASE_BOOL: {
			switch(tk2) {
				case DYN: return tag_value(x, G_BOOL); // define x:G=>? as dynamic type value
				default: break;
			}
			break;
		}
		case BASE_UNIT: {
			switch(tk2) {
				case DYN: return tag_value(x, G_UNIT); // define x:G=>? as dynamic type value
				default: break;
			}
			break;
		}
		case TYFUN: {
			switch(tk2) {
				case TYFUN: { 				// when t1 and t2 are function type
					#ifdef PROFILE
					int cur = 1;
					fun *tmp = (fun*)x;
					while(tmp->funcM != fun_wrapped_call_funcM) {
						cur++;
						tmp = (fun*)tmp->env[0];
					}
					update_longest(cur);
					#endif
					value retx;
					// printf("defined as a wrapped function\n");						// define x:U1->U2=>U3->U4 as wrapped function
					retx = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * 5);
					((fun*)retx)->funcM = fun_wrapped_call_funcM;
					((fun*)retx)->env[0] = (void*)((fun*)x);
					((fun*)retx)->env[1] = (void*)t1;
					((fun*)retx)->env[2] = (void*)t2;
					((fun*)retx)->env[3] = (void*)(uintptr_t)rid;
					((fun*)retx)->env[4] = (void*)(uintptr_t)polarity;
					return retx;
				}
				case DYN: {
					if (t1->tydat.tyfun.left->tykind == DYN && t1->tydat.tyfun.right->tykind == DYN) {
						#ifdef PROFILE
						int cur = 1;
						fun *tmp = (fun*)x;
						while(tmp->funcM != fun_wrapped_call_funcM) {
							cur++;
							tmp = (fun*)tmp->env[0];
						}
						update_longest(cur);
						#endif
						return tag_value(x, G_AR); // define x:G=>? as dynamic type value
					} else {			// when t1 is function type and t2 is ?
						// printf("cast ground\n");
						value x_ = cast(x, t1, &tyar, rid, polarity);									// R_GROUND (x:U=>? -> x:U=>G=>?)
						return cast(x_, &tyar, t2, rid, polarity);
					}
				}
				default: break;
			}
			break;
		}
		case TYLIST: {
			switch(tk2) {
				case TYLIST: {
					#ifdef EAGER
					value retv = 0;
    				value *dest = &retv;
    				value curr_src = x;
					ty *tylist1 = t1->tydat.tylist;
					ty *tylist2 = t2->tydat.tylist;
    				while((lst*)curr_src != NULL) {
    				    lst *new_lst = (lst*)GC_MALLOC(sizeof(lst));
    				    *dest = (value)new_lst;
    				    new_lst->h = cast(((lst*)curr_src)->h, tylist1, tylist2, rid, polarity);
    				    dest = &new_lst->t;
    				    curr_src = ((lst*)curr_src)->t;
    				}
    				*dest = (value)NULL;
    				return retv;
					#else
					#ifdef PROFILE
					int cur = 1;
					lst *tmp = (lst*)x;
					while(tmp->t & 0b1 != 1) {
						cur++;
						tmp = tmp->w;
					}
					update_longest(cur);
					#endif
					value retx;
					// printf("defined as a wrapped list\n");						// define x:[U1]=>[U2] as wrapped list
					retx = (value)GC_MALLOC(sizeof(lst));
					((lst*)retx)->w = (lst*)x;
					((lst*)retx)->wrap_info.u1_tag = (uintptr_t)t1 | 0b1;
					((lst*)retx)->wrap_info.u2_p = (uintptr_t)t2 | polarity;
					((lst*)retx)->wrap_info.rid = rid;
					return retx;
					#endif
				}
				case DYN: {
					if (t1->tydat.tylist->tykind == DYN) {
						#ifdef PROFILE
						int cur = 1;
						#ifdef EAGER
						update_longest(1);
						#else
						lst *tmp = (lst*)x;
						while(tmp->t & 0b1 != 1) {
							cur++;
							tmp = tmp->w;
						}
						update_longest(cur);
						#endif
						#endif
						return tag_value(x, G_LI); // define x:G=>? as dynamic type value
					} else {			// when t1 is list type and t2 is ?
						// printf("cast ground\n");
						value x_ = cast(x, t1, &tyli, rid, polarity);									// R_GROUND (x:U=>? -> x:U=>G=>?)
						return cast(x_, &tyli, t2, rid, polarity);
					}
				}
				default: break;
			}
			break;
		}
		case TYTUPLE: {
			uint16_t arity = t1->tydat.tytuple.arity;
			switch(tk2) {
				case TYTUPLE: {
					#ifdef EAGER
					value retv = (value)GC_MALLOC(sizeof(tpl) + sizeof(value) * arity);
					((tpl*)retv)->hdr.arity = arity;
					for (int i = 0; i < arity; i++) {
						value inner_val = ((tpl*)x)->fields[i];
						((tpl*)retv)->fields[i] = cast(inner_val, t1->tydat.tytuple.tys[i], t2->tydat.tytuple.tys[i], rid, polarity);
					}
					return retv;

					#else // not EAGER
					#ifdef PROFILE
					int cur = 1;
					tpl *tmp = (tpl*)x;
					while(tmp->wrap == 1) {
						cur++;
						tmp = (tpl*)((tpl_wrap*)tmp)->w;
					}
					update_longest(cur);
					#endif
					value retx = (value)GC_MALLOC(sizeof(tpl_wrap));
					((tpl_wrap*)retx)->hdr.arity = arity;
					((tpl_wrap*)retx)->hdr.wrap = 1;
                    ((tpl_wrap*)retx)->hdr.rid = rid;
                    ((tpl_wrap*)retx)->hdr.polarity = polarity;
					((tpl_wrap*)retx)->w = (tpl*)x;
					((tpl_wrap*)retx)->u1 = t1->tydat.tytuple.tys;
					((tpl_wrap*)retx)->u2 = t2->tydat.tytuple.tys;
					return retx;
					#endif
				}
				case DYN: {
					int all_dyn = 1;
					for(int i = 0; i < arity; i++) {
						if (t1->tydat.tytuple.tys[i]->tykind != DYN) { all_dyn = 0; break; }
					}
					if (all_dyn) {
						#ifdef PROFILE
						int cur = 1;
						#ifdef EAGER
						update_longest(1);
						#else
						tpl *tmp = (tpl*)x;
						while(tmp->wrap != 1) {
							cur++;
							tmp = (tpl*)((tpl_wrap*)tmp)->w;
						}
						update_longest(cur);
						#endif
						#endif
						return tag_value(x, G_TP);
					} else {
						ty *dyn_tuple = get_dyn_tuple_ty(arity);
						value x_ = cast(x, t1, dyn_tuple, rid, polarity);
						return cast(x_, dyn_tuple, t2, rid, polarity);
					}
				}
				default: break;
			}
			break;
		}
		case DYN: {
			switch(tk2) {
				case BASE_INT: {			// when t1 is ? and t2 is ground type
					if (tag_of(x) == G_INT) {													// when t1's injection ground type equals t2
						// printf("cast success\n");										// R_SUCCEED (x':G=>?=>G -> x')
						return untag_value(x, G_INT);
					} else {											// when t1's injection ground type dosen't equal t2
						// printf("cast fail. t:%d, t_:%d\n", t, G_INT);											// E_FAIL (x':G1=>?=>G2 if G1<>G2 -> blame)
						blame(rid, polarity);
					}
				}
				case BASE_BOOL: {
					if (tag_of(x) == G_BOOL) {													// when t1's injection ground type equals t2
						// printf("cast success\n");										// R_SUCCEED (x':G=>?=>G -> x')
						return untag_value(x, G_BOOL);
					} else {											// when t1's injection ground type dosen't equal t2
						// printf("cast fail. t:%d, t_:%d\n", x.d->g, G_BOOL);											// E_FAIL (x':G1=>?=>G2 if G1<>G2 -> blame)
						blame(rid, polarity);
					}
				}
				case BASE_UNIT: {
					if (tag_of(x) == G_UNIT) {													// when t1's injection ground type equals t2
						// printf("cast success\n");										// R_SUCCEED (x':G=>?=>G -> x')
						return untag_value(x, G_UNIT);
					} else {											// when t1's injection ground type dosen't equal t2
						// printf("cast fail. t:%d, t_:%d\n", x.d->g, G_UNIT);											// E_FAIL (x':G1=>?=>G2 if G1<>G2 -> blame)
						blame(rid, polarity);
					}
				}
				case TYFUN: {
					if (t2->tydat.tyfun.left->tykind == DYN && t2->tydat.tyfun.right->tykind == DYN) {
						if (tag_of(x) == G_AR) {													// when t1's injection ground type equals t2
							// printf("cast success\n");										// R_SUCCEED (x':G=>?=>G -> x')
							return untag_value(x, G_AR);
						} else {											// when t1's injection ground type dosen't equal t2
							// printf("cast fail. t:%d, t_:%d\n", x.d->g, G_AR);											// E_FAIL (x':G1=>?=>G2 if G1<>G2 -> blame)
							blame(rid, polarity);
						}
					} else {			// when t1 is ? and t2 is function type
						// printf("cast expand\n");
						value x_ = cast(x, t1, &tyar, rid, polarity);									// R_EXPAND (x:?=>U -> x:?=>G=>U)
						return cast(x_, &tyar, t2, rid, polarity);
					}
				}
				case TYLIST: {
					if (t2->tydat.tylist->tykind == DYN) {
						if (tag_of(x) == G_LI) {													// when t1's injection ground type equals t2
							// printf("cast success\n");										// R_SUCCEED (x':G=>?=>G -> x')
							return untag_value(x, G_LI);
						} else {											// when t1's injection ground type dosen't equal t2
							// printf("cast fail. t:%d, t_:%d\n", x.d->g, G_LI);											// E_FAIL (x':G1=>?=>G2 if G1<>G2 -> blame)
							blame(rid, polarity);
						}
					} else {			// when t1 is ? and t2 is function type
						// printf("cast expand\n");
						value x_ = cast(x, t1, &tyli, rid, polarity);									// R_EXPAND (x:?=>U -> x:?=>G=>U)
						return cast(x_, &tyli, t2, rid, polarity); 
					}
				}
				case TYTUPLE: {
					int all_dyn = 1;
					uint16_t arity = t2->tydat.tytuple.arity;
					for(int i = 0; i < arity; i++) {
						if (t2->tydat.tytuple.tys[i]->tykind != DYN) { all_dyn = 0; break; }
					}
					if (all_dyn) {
						if (tag_of(x) == G_TP) {
							value t = untag_value(x, G_TP);
							if (((tpl*)t)->arity == arity) {
								return t;
							} else {
								blame(rid, polarity);
							}
						} else {
							blame(rid, polarity);
						}
					} else {
						if (tag_of(x) == G_TP) {
							ty *dyn_tuple = get_dyn_tuple_ty(((tpl*)untag_value(x, G_TP))->arity);
							value x_ = cast(x, t1, dyn_tuple, rid, polarity);
							return cast(x_, dyn_tuple, t2, rid, polarity); 
						} else {
							blame(rid, polarity);
						}
					}
				}
				case TYVAR: {			// when t1 is ? and t2 is type variable
					switch(tag_of(x)) {
						case(G_INT): {											// when t1's injection ground type is int
							// printf("DTI : int was inferred\n");							// R_INSTBASE (x':int=>?=>X -[X:=int]> x')
							#ifdef PROFILE
							current_inference++;
							#endif
							*t2 = tyint;
							return untag_value(x, G_INT);
						}
						case(G_BOOL): {												// when t1's injection ground type is bool	
							// printf("DTI : bool was inferred\n");							// R_INSTBASE (x':bool=>?=>X -[X:=bool]> x')
							#ifdef PROFILE
							current_inference++;
							#endif
							*t2 = tybool;
							return untag_value(x, G_BOOL);
						}
						case(G_UNIT): {											// when t1's injection ground type is unit
							// printf("DTI : unit was inferred\n");							// R_INSTBASE (x':unit=>?=>X -[X:=unit]> x')
							#ifdef PROFILE
							current_inference++;
							#endif
							*t2 = tyunit;
							return untag_value(x, G_UNIT);
						}
						case(G_AR):	{												// when t1's injection ground type is ?->?
							// printf("DTI : arrow was inferenced\n");							// R_INSTARROW (x':?->?=>?=>X -[X:=X_1->X_2]> x':?->?=>X_1->X_2)
							#ifdef PROFILE
							current_inference++;
							#endif
							t2->tykind = TYFUN;
							t2->tydat.tyfun.left = (ty*)GC_MALLOC(sizeof(ty));
							t2->tydat.tyfun.right = (ty*)GC_MALLOC(sizeof(ty));
							t2->tydat.tyfun.left->tykind = TYVAR;
							t2->tydat.tyfun.right->tykind = TYVAR;
							return cast(untag_value(x, G_AR), &tyar, t2, rid, polarity);
						}
						case(G_LI):	{												// when t1's injection ground type is [?]
							// printf("DTI : list was inferenced\n");							// R_INSTLIST (x':[?]=>?=>X -[X:=[X_1]]> x':[?]=>[X_1])
							#ifdef PROFILE
							current_inference++;
							#endif
							t2->tykind = TYLIST;
							t2->tydat.tylist = (ty*)GC_MALLOC(sizeof(ty));
							t2->tydat.tylist->tykind = TYVAR;
							return cast(untag_value(x, G_LI), &tyli, t2, rid, polarity);
						}
						case(G_TP):	{												// when t1's injection ground type is (?,...,?)
							// printf("DTI : list was inferenced\n");							// R_INSTTUPLE (x':(?,...,?)=>?=>X -[X:=(X_1,...,Xn)]> x':(?,...,?)=>(X_1,...,Xn))
							#ifdef PROFILE
							current_inference++;
							#endif
							uint16_t arity = ((tpl*)untag_value(x, G_TP))->arity;
							t2->tykind = TYTUPLE;
							t2->tydat.tytuple.arity = arity;
							t2->tydat.tytuple.tys = (ty**)GC_MALLOC(sizeof(ty*) * arity);
							ty *new_tvs = (ty*)GC_MALLOC(sizeof(ty) * arity);
							for (int i = 0; i < arity; i++) {
								t2->tydat.tytuple.tys[i] = &new_tvs[i];
								t2->tydat.tytuple.tys[i]->tykind = TYVAR;
							}
							return cast(untag_value(x, G_TP), get_dyn_tuple_ty(arity), t2, rid, polarity);
						}
					}
				}
				case DYN: {
					printf("Dyn and Dyn should be omitted by id");
					exit(1);
				}
			}
		}
		default: break;
	}
	
	printf("cast cannot be resolved. t1: %d, t2: %d\n", t1->tykind, t2->tykind);
	exit(1);
}
#else // CAST
value coerce(value v, crc *s) {
	// printf("coerce c:%d\n", s->crckind);
	#ifdef PROFILE
	current_cast++;
	#endif
	if (s == &crc_id) return v; // v<id> -> v
	if (s == &crc_inj_INT) return tag_value(v, G_INT);
	if (s == &crc_inj_BOOL) return tag_value(v, G_BOOL);
	if (s == &crc_inj_UNIT) return tag_value(v, G_UNIT);
	if (s == &crc_inj_AR) return tag_value(v, G_AR);
	if (s == &crc_inj_LI) return tag_value(v, G_LI);
	crc *mid_crc;
	switch (s->crckind) {
		case ID: goto OPTIMIZATION_UNCAUGHT;
		case BOT: 
		CASE_BOT: blame(s->crcdat.seq_tv.rid_proj, s->p_proj); // v<bot^p> -> blame p
		case FUN: 
		CASE_FUN: { // v<s'=>t'>
			if (((fun*)v)->funcD == fun_wrapped_call_funcD) { // u<<s=>t>><s'=>t'>
				crc *c = compose_funs((crc*)((fun*)v)->env[1], s);
				if (c->crckind == ID) {    // u<<s=>t>><s'=>t'> -> u<id> -> u
					return (value)(fun*)((fun*)v)->env[0];
				} else {										 // u<<s=>t>><s'=>t'> -> u<s';;s=>t;;t'> -> u<<s';;s=>t;;t'>>
					value retv;
					retv = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * 2);
					((fun*)retv)->funcD = fun_wrapped_call_funcD;
					#ifdef ALT
					((fun*)retv)->funcM = fun_wrapped_call_funcM;
					#endif // ALT
					((fun*)retv)->env[0] = (void*)((fun*)v)->env[0];
					((fun*)retv)->env[1] = (void*)c;
					return retv;
				}
			} else {                   // u<s'=>t'> -> u<<s'=>t'>>
				#ifdef PROFILE
				update_longest(1);
				#endif
				value retv;
				retv = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * 2);
				((fun*)retv)->funcD = fun_wrapped_call_funcD;
				#ifdef ALT
				((fun*)retv)->funcM = fun_wrapped_call_funcM;
				#endif // ALT
				((fun*)retv)->env[0] = (void*)(fun*)v;
				((fun*)retv)->env[1] = (void*)s;
				return retv;
			}
		}
		case LIST: 
		CASE_LIST: { // v<[s']>
			#ifdef EAGER
			value retv = 0;
    		value *dest = &retv;
    		value curr_src = v;
			crc *clist = s->crcdat.lst_crc;
    		while ((lst*)curr_src != NULL) {
    		    lst *new_lst = (lst*)GC_MALLOC(sizeof(lst));
    		    *dest = (value)new_lst;
    		    new_lst->h = coerce(((lst*)curr_src)->h, clist);
    		    dest = &new_lst->t;
    		    curr_src = ((lst*)curr_src)->t;
    		}
    		*dest = 0;
    		return retv;
			#else
			if ((lst*)v != NULL && (((lst*)v)->t & 0b1)) { // u<<[s]>><[s']>
				crc *c = compose_lists((crc*)(((lst*)v)->t & ~0b1), s);
				if (c->crckind == ID) {    						// u<<[s]>><[s']> -> u<id> -> u
					return (value)((lst*)v)->w;
				} else {										// u<<[s]>><[s']> -> u<[s;;s']> -> u<<[s;;s']>>
					value retv;
					retv = (value)GC_MALLOC(sizeof(lst));
					((lst*)retv)->w = ((lst*)v)->w;
					((lst*)retv)->c_tag = (uintptr_t)c | 0b1;
					return retv;
				}
			} else {                   // u<[s']> -> u<<[s']>>
				#ifdef PROFILE
				update_longest(1);
				#endif
				value retv;
				retv = (value)GC_MALLOC(sizeof(lst));
				((lst*)retv)->w = (lst*)v;
				((lst*)retv)->c_tag = (uintptr_t)s | 0b1;
				return retv;
			}
			#endif
		}
		case TUPLE: 
		CASE_TUPLE: { // v<(s1*...*sn)>
			uint16_t arity = s->crcdat.tpl_crc.arity;
			#ifdef EAGER
			value retv = (value)GC_MALLOC(sizeof(tpl) + sizeof(value) * arity);
			((tpl*)retv)->hdr.arity = arity;
			for (int i = 0; i < arity; i++) {
				value inner_val = ((tpl*)v)->fields[i];
				((tpl*)retv)->fields[i] = coerce(inner_val, s->crcdat.tpl_crc.crcs[i]);
			}
			return retv;

			#else // not EAGER
			value retv = (value)GC_MALLOC(sizeof(tpl_wrap));
			((tpl_wrap*)retv)->hdr.arity = arity;
			((tpl_wrap*)retv)->hdr.wrap = 1;

			if (((tpl*)v)->wrap) { // u<<(s1*...*sn)>><(s'1*...*s'n)>
				crc *c = compose_tuples(((tpl_wrap*)v)->c, s);
				if (c->crckind == ID) {    // u<<(s1*...*sn)>><(s'1*...*s'n)> -> u<id> -> u
					return (value)((tpl_wrap*)v)->w;
				} else {
					((tpl_wrap*)retv)->w = ((tpl_wrap*)v)->w;
					((tpl_wrap*)retv)->c = c;
					return retv;
				}
			} else { // u<(s'1*...*s'n)> -> u<<(s'1*...*s'n)>>
				#ifdef PROFILE
				update_longest(1);
				#endif
				((tpl_wrap*)retv)->w = (tpl*)v;
				((tpl_wrap*)retv)->c = s;
				return retv;
			}
			#endif
		}
		case TV_INJ: {
			s->crcdat.seq_tv.ptr.tv = ty_find(s->crcdat.seq_tv.ptr.tv);
			s = normalize_tv_inj(s);
			if (s == &crc_inj_INT) return tag_value(v, G_INT);
			if (s == &crc_inj_BOOL) return tag_value(v, G_BOOL);
			if (s == &crc_inj_UNIT) return tag_value(v, G_UNIT);
			// fallthrough
		}
		case SEQ_INJ: {
			mid_crc = s->crcdat.seq_tv.ptr.s;
			switch(mid_crc->crckind) {
				case FUN: 
				CASE_SEQ_INJ_FUN: { // v<s'=>t';G!>
					value retv;
					retv = (value)GC_MALLOC(sizeof(fun) + sizeof(void*) * 2);
					((fun*)retv)->funcD = fun_wrapped_call_funcD;
					#ifdef ALT
					((fun*)retv)->funcM = fun_wrapped_call_funcM;
					#endif // ALT
					if (((fun*)v)->funcD == fun_wrapped_call_funcD) {  // u<<s=>t>><s'=>t';G!>
						((fun*)retv)->env[0] = ((fun*)v)->env[0];
						((fun*)retv)->env[1] = (void*)compose_funs((crc*)((fun*)v)->env[1], mid_crc);
					} else { // u<s'=>t';G!> -> u<<s'=>t';G!>>
						#ifdef PROFILE
						update_longest(1);
						#endif
						((fun*)retv)->env[0] = (void*)v;
						((fun*)retv)->env[1] = (void*)mid_crc;
					}
					return tag_value(retv, G_AR);
				}
				case LIST: 
				CASE_SEQ_INJ_LIST: { // v<[s'];G!>
					#ifdef EAGER
					#ifdef PROFILE
					update_longest(1);
					#endif
					value retv = 0;
    				value *dest = &retv;
    				value curr_src = v;
					crc *clist = mid_crc->crcdat.lst_crc;
    				while ((lst*)curr_src != NULL) {
    				    lst *new_lst = (lst*)GC_MALLOC(sizeof(lst));
    				    *dest = (value)new_lst;
    				    new_lst->h = coerce(((lst*)curr_src)->h, clist);
    				    dest = &new_lst->t;
    				    curr_src = ((lst*)curr_src)->t;
    				}
    				*dest = 0;
    				return tag_value(retv, G_LI);
					#else
					value retv;
					retv = (value)GC_MALLOC(sizeof(lst));
					if ((lst*)v != NULL && (((lst*)v)->c_tag & 0b1)) {   // u<<[s]>><[s'];G!>
						((lst*)retv)->w = ((lst*)v)->w;
						((lst*)retv)->c_tag = (uintptr_t)compose_lists((crc*)(((lst*)v)->c_tag & ~0b1), mid_crc) | 0b1;
					} else { // u<[s'];G!> -> u<<[s'];G!>>
						#ifdef PROFILE
						update_longest(1);
						#endif
						((lst*)retv)->w = (lst*)v;
						((lst*)retv)->c_tag = (uintptr_t)mid_crc | 0b1;
					}
					return tag_value(retv, G_LI);
					#endif
				}
				case TUPLE: 
				CASE_SEQ_INJ_TUPLE: { // v<(s'1*...*s'n);G!>
					uint16_t arity = mid_crc->crcdat.tpl_crc.arity;
					#ifdef EAGER
					#ifdef PROFILE
					update_longest(1);
					#endif
					value retv = (value)GC_MALLOC(sizeof(tpl) + sizeof(value) * arity);
					((tpl*)retv)->hdr.arity = arity;
					for (int i = 0; i < arity; i++) {
						value inner_val = ((tpl_raw*)v)->fields[i];
						((tpl_raw*)retv)->fields[i] = coerce(inner_val, mid_crc->crcdat.tpl_crc.crcs[i]);
					}
					return tag_value(retv, G_TP);
					#else // not EAGER
					value retv = (value)GC_MALLOC(sizeof(tpl_wrap));
					((tpl_wrap*)retv)->hdr.arity = arity;
					((tpl_wrap*)retv)->hdr.wrap = 1;
					if (v != 0 && ((tpl*)v)->wrap) {   // u<<(s1*...*sn)>><(s'1*...*s'n);G!>
						((tpl_wrap*)retv)->w = ((tpl_wrap*)v)->w;
						((tpl_wrap*)retv)->c = compose_tuples(((tpl_wrap*)v)->c, mid_crc);
					} else { // u<(s'1*...*s'n);G!> -> u<<(s'1*...*s'n);G!>>
						#ifdef PROFILE
						update_longest(1);
						#endif
						((tpl_wrap*)retv)->w = (tpl*)v;
						((tpl_wrap*)retv)->c = mid_crc;
					}
					return tag_value((value)retv, G_TP);
					#endif
				}
				default: { // v<id;G!> -> v<<id;G!>>
					return tag_value(v, s->g_inj);
					// goto OPTIMIZATION_UNCAUGHT;
				}	
			}
		}

		case TV_PROJ: { // v<X?p> = u<<d>><X?p>
			s->crcdat.seq_tv.ptr.tv = ty_find(s->crcdat.seq_tv.ptr.tv);
			s = normalize_tv_proj(s);
			if (s->crckind != TV_PROJ) goto CASE_SEQ_PROJ;
			dti(tag_of(v), arity_of(v), s->crcdat.seq_tv.ptr.tv);
			s = normalize_tv_proj(s);
			goto CASE_SEQ_PROJ;
		}

		case TV_PROJ_INJ: { // v<?pX!> = u<<d>><?pX!>
			s->crcdat.seq_tv.ptr.tv = ty_find(s->crcdat.seq_tv.ptr.tv);
			s = normalize_tv_proj_inj(s);
			if (s->crckind != TV_PROJ_INJ) goto CASE_SEQ_PROJ_INJ;
			dti(tag_of(v), arity_of(v), s->crcdat.seq_tv.ptr.tv);
			s = normalize_tv_proj_inj(s);
			goto CASE_SEQ_PROJ_INJ;
		}

		case TV_PROJ_OCCUR: {
			s->crcdat.seq_tv.ptr.tv = ty_find(s->crcdat.seq_tv.ptr.tv);
			s = normalize_tv_proj_occur(s);
			if (s->crckind != TV_PROJ_OCCUR) goto CASE_SEQ_PROJ_BOT;
			dti(tag_of(v), arity_of(v), s->crcdat.seq_tv.ptr.tv);
			s = normalize_tv_proj_occur(s);
			goto CASE_SEQ_PROJ_BOT;
		}

		case SEQ_PROJ: 
		CASE_SEQ_PROJ: {				// v<G?p;g> = u<<d>><G?p;g>
			uint8_t tag = tag_of(v);
			if (tag != s->g_proj) blame(s->crcdat.seq_tv.rid_proj, s->p_proj);

			v = untag_value(v, tag);
			s = s->crcdat.seq_tv.ptr.s;

			if (s == &crc_id) return v; // u<<d>><s> -> u<id> -> u

			switch(s->crckind) {
				case ID: goto OPTIMIZATION_UNCAUGHT;
				case FUN: goto CASE_FUN;
				case LIST: goto CASE_LIST;
				case TUPLE: goto CASE_TUPLE;
				default: {
					printf("seq_proj should have only g\n");
					exit(1);
				}
			}
		}

		case SEQ_PROJ_INJ: 
		CASE_SEQ_PROJ_INJ: {
			uint8_t tag = tag_of(v);
			if (tag != s->g_proj) blame(s->crcdat.seq_tv.rid_proj, s->p_proj);

			v = untag_value(v, tag);
			mid_crc = s->crcdat.seq_tv.ptr.s;

			if (mid_crc == &crc_id) return tag_value(v, s->g_inj); // u<<d>><s> -> u<id> -> u

			switch(mid_crc->crckind) {
				case ID: goto OPTIMIZATION_UNCAUGHT;
				case FUN: goto CASE_SEQ_INJ_FUN;
				case LIST: goto CASE_SEQ_INJ_LIST;
				case TUPLE: goto CASE_SEQ_INJ_TUPLE;
				default: {    // u<<d>><s> -> u<g;G!> -> u<<g;G!>>
					printf("seq_proj should have only g\n");
					exit(1);
				}
			}
		}

		case SEQ_PROJ_BOT: 
		CASE_SEQ_PROJ_BOT: {
			uint8_t tag = tag_of(v);
			if (tag != s->g_proj) blame(s->crcdat.seq_tv.rid_proj, s->p_proj);
			s = s->crcdat.seq_tv.ptr.s;
			goto CASE_BOT;
		}
	}

	OPTIMIZATION_UNCAUGHT: 
	printf("optimization for coercion %d is not caught", s->crckind);
	exit(1);
}		
#endif	

__attribute__((noreturn)) void blame(uint32_t rid, uint8_t polarity) {
	if(polarity == 1) {
		printf("Blame on the expression side:\n");
	} else {
		printf("Blame on the environment side:\n");
	}
	range r = range_list[rid];
	printf("%sline %d, character %d -- line %d, character %d\n", r.filename, r.startline, r.startchr, r.endline, r.endchr);
	exit(0);
}

#endif