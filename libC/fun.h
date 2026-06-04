#ifndef FUN_H
#define FUN_H

#include "types.h"

typedef struct fun {
    // 第一引数に 自分自身のクロージャ cls を受け取る
	// クロージャを生成しないDirの適用であれば、envにはdummyのvalueを入れて対処
    #if defined(ALT)
    value (*funcM)(value, value);
    value (*funcD)(value, value, value);
    #else //ALT
    // 型適用だけをするための関数が常にfuncMを使えるように、STATICやCAST以外のときにもfuncMを定義
    union {
        value (*funcM)(value, value);
        value (*funcD)(value, value, value);
    };
    #endif
	
	// 自由変数や型引数、Wrapであればcoercionや型情報など
    void* env[];
} fun;

/* 
 * メモリレイアウトの例 (すべて void* にキャストして格納)
 * (A) 普通のクロージャ (自由変数がx, yの2つ)
 * [ funcM / funcD ]
 * [ env[0] = (void*)x  ] <-- value x = *(value*)&env[0] として取り出す
 * [ env[1] = (void*)y  ]
 *
 * (B) 多相クロージャ (自由変数がx、型引数がty1)
 * [ funcM / funcD ]
 * [ env[0] = (void*)x   ]
 * [ env[1] = (void*)ty1 ] <-- ty* ty1 = (ty*)env[1] として取り出す
 *
 * (C) WRAPされたクロージャ (CASTオフ時)
 * [ funcM / funcD = fun_wrapped_call_funcM / fun_wrapped_call_funcD ]
 * [ env[0] = (void*)元の関数(fun*)  ]
 * [ env[1] = (void*)コアーション(crc*) ]
 * 
 * (D) WRAPされたクロージャ (CASTオン時): (\x. ...): t1 =>^r_p t2
 * [ funcM = fun_wrapped_call_funcM ]
 * [ env[0] = (void*)元の関数(fun*)  ]
 * [ env[1] = (void*)t1(ty*) ]
 * [ env[2] = (void*)t2(ty*) ]
 * [ env[3] = (void*)(uintptr_t)rid ]
 * [ env[4] = (void*)(uintptr_t)polarity ]
 */

/*
 * wrap関数であるかどうかの判定は
 * 関数ポインタのアドレスがトランポリン関数のアドレスと一致するかで行う。
 */

#endif