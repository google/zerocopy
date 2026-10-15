let subroutine_signatures = [
("aes_xts_decrypt",
  ([(*args*)
     ("in", "uint8_t*", (*is const?*)"true");
     ("out", "uint8_t*", (*is const?*)"false");
     ("length", "size_t", (*is const?*)"false");
     ("key1", "s2n_bignum_AES_KEY*", (*is const?*)"true");
     ("key2", "s2n_bignum_AES_KEY*", (*is const?*)"true");
     ("iv", "uint8_t[static 16]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("in", "length"(* num elems *), 1(* elem bytesize *));
    ("key1", "244"(* num elems *), 1(* elem bytesize *));
    ("key2", "244"(* num elems *), 1(* elem bytesize *));
    ("iv", "16"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("out", "length"(* num elems *), 1(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("aes_xts_encrypt",
  ([(*args*)
     ("in", "uint8_t*", (*is const?*)"true");
     ("out", "uint8_t*", (*is const?*)"false");
     ("length", "size_t", (*is const?*)"false");
     ("key1", "s2n_bignum_AES_KEY*", (*is const?*)"true");
     ("key2", "s2n_bignum_AES_KEY*", (*is const?*)"true");
     ("iv", "uint8_t[static 16]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("in", "length"(* num elems *), 1(* elem bytesize *));
    ("key1", "244"(* num elems *), 1(* elem bytesize *));
    ("key2", "244"(* num elems *), 1(* elem bytesize *));
    ("iv", "16"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("out", "length"(* num elems *), 1(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_add",
  ([(*args*)
     ("p", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("m", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("n", "uint64_t", (*is const?*)"false");
     ("y", "uint64_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "m"(* num elems *), 8(* elem bytesize *));
    ("y", "n"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "p"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_add_p25519",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
     ("y", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
    ("y", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_add_p256",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
     ("y", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
    ("y", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_add_p256k1",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
     ("y", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
    ("y", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_add_p384",
  ([(*args*)
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
     ("y", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
    ("y", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_add_p521",
  ([(*args*)
     ("z", "uint64_t[static 9]", (*is const?*)"false");
     ("x", "uint64_t[static 9]", (*is const?*)"true");
     ("y", "uint64_t[static 9]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "9"(* num elems *), 8(* elem bytesize *));
    ("y", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_add_sm2",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
     ("y", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
    ("y", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_amontifier",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("m", "uint64_t*", (*is const?*)"true");
     ("t", "uint64_t*", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("m", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
    ("t", ">=k"(* num elems *), 8(* elem bytesize *));
   ])
);

("bignum_amontmul",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("y", "uint64_t*", (*is const?*)"true");
     ("m", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
    ("y", "k"(* num elems *), 8(* elem bytesize *));
    ("m", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_amontredc",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("n", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("m", "uint64_t*", (*is const?*)"true");
     ("p", "uint64_t", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("x", "n"(* num elems *), 8(* elem bytesize *));
    ("m", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_amontsqr",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("m", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
    ("m", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_bigendian_4",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_bigendian_6",
  ([(*args*)
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_bitfield",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("n", "uint64_t", (*is const?*)"false");
     ("l", "uint64_t", (*is const?*)"false");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("bignum_bitsize",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("bignum_cdiv",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("n", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("m", "uint64_t", (*is const?*)"false");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "n"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_cdiv_exact",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("n", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("m", "uint64_t", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("x", "n"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_cld",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("bignum_clz",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("bignum_cmadd",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("c", "uint64_t", (*is const?*)"false");
     ("n", "uint64_t", (*is const?*)"false");
     ("y", "uint64_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("y", "n"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_cmnegadd",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("c", "uint64_t", (*is const?*)"false");
     ("n", "uint64_t", (*is const?*)"false");
     ("y", "uint64_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("y", "n"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_cmod",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("m", "uint64_t", (*is const?*)"false");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("bignum_cmul",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("c", "uint64_t", (*is const?*)"false");
     ("n", "uint64_t", (*is const?*)"false");
     ("y", "uint64_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("y", "n"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_cmul_p25519",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("c", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_cmul_p256",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("c", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_cmul_p256k1",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("c", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_cmul_p384",
  ([(*args*)
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("c", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_cmul_p521",
  ([(*args*)
     ("z", "uint64_t[static 9]", (*is const?*)"false");
     ("c", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t[static 9]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_cmul_sm2",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("c", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_coprime",
  ([(*args*)
     ("m", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("n", "uint64_t", (*is const?*)"false");
     ("y", "uint64_t*", (*is const?*)"true");
     ("t", "uint64_t*", (*is const?*)"false");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "m"(* num elems *), 8(* elem bytesize *));
    ("y", "n"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
    ("t", ">=2*max(m,n)"(* num elems *), 8(* elem bytesize *));
   ])
);

("bignum_copy",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("n", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "n"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_copy_row_from_table",
  ([(*args*)
     ("z", "uint64_t*", (*is const?*)"false");
     ("table", "uint64_t*", (*is const?*)"true");
     ("height", "uint64_t", (*is const?*)"false");
     ("width", "uint64_t", (*is const?*)"false");
     ("idx", "uint64_t", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("table", "height*width"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "width"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_copy_row_from_table_16",
  ([(*args*)
     ("z", "uint64_t*", (*is const?*)"false");
     ("table", "uint64_t*", (*is const?*)"true");
     ("height", "uint64_t", (*is const?*)"false");
     ("idx", "uint64_t", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("table", "height*16"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "16"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_copy_row_from_table_32",
  ([(*args*)
     ("z", "uint64_t*", (*is const?*)"false");
     ("table", "uint64_t*", (*is const?*)"true");
     ("height", "uint64_t", (*is const?*)"false");
     ("idx", "uint64_t", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("table", "height*32"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "32"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_copy_row_from_table_8n",
  ([(*args*)
     ("z", "uint64_t*", (*is const?*)"false");
     ("table", "uint64_t*", (*is const?*)"true");
     ("height", "uint64_t", (*is const?*)"false");
     ("width", "uint64_t", (*is const?*)"false");
     ("idx", "uint64_t", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("table", "height*width"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "width"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_ctd",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("bignum_ctz",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("bignum_deamont_p256",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_deamont_p256k1",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_deamont_p384",
  ([(*args*)
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_deamont_p521",
  ([(*args*)
     ("z", "uint64_t[static 9]", (*is const?*)"false");
     ("x", "uint64_t[static 9]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_deamont_sm2",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_demont",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("m", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
    ("m", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_demont_p256",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_demont_p256k1",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_demont_p384",
  ([(*args*)
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_demont_p521",
  ([(*args*)
     ("z", "uint64_t[static 9]", (*is const?*)"false");
     ("x", "uint64_t[static 9]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_demont_sm2",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_digit",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("n", "uint64_t", (*is const?*)"false");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("bignum_digitsize",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("bignum_divmod10",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
   ],
   "uint64_t",
   [(* input buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_double_p25519",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_double_p256",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_double_p256k1",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_double_p384",
  ([(*args*)
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_double_p521",
  ([(*args*)
     ("z", "uint64_t[static 9]", (*is const?*)"false");
     ("x", "uint64_t[static 9]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_double_sm2",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_emontredc",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("m", "uint64_t*", (*is const?*)"true");
     ("w", "uint64_t", (*is const?*)"false");
   ],
   "uint64_t",
   [(* input buffers *)
    ("z", "2*k"(* num elems *), 8(* elem bytesize *));
    ("m", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "2*k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_emontredc_8n",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("m", "uint64_t*", (*is const?*)"true");
     ("w", "uint64_t", (*is const?*)"false");
   ],
   "uint64_t",
   [(* input buffers *)
    ("z", "2*k"(* num elems *), 8(* elem bytesize *));
    ("m", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "2*k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_emontredc_8n_cdiff",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("m", "uint64_t*", (*is const?*)"true");
     ("w", "uint64_t", (*is const?*)"false");
     ("m_precalc", "uint64_t*", (*is const?*)"false");
   ],
   "uint64_t",
   [(* input buffers *)
    ("z", "2*k"(* num elems *), 8(* elem bytesize *));
    ("m", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "2*k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
    ("m_precalc", "12*(k/4-1)"(* num elems *), 8(* elem bytesize *));
   ])
);

("bignum_eq",
  ([(*args*)
     ("m", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("n", "uint64_t", (*is const?*)"false");
     ("y", "uint64_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "m"(* num elems *), 8(* elem bytesize *));
    ("y", "n"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("bignum_even",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("bignum_frombebytes_4",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint8_t[static 32]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "32"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_frombebytes_6",
  ([(*args*)
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("x", "uint8_t[static 48]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "48"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_fromlebytes_4",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint8_t[static 32]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "32"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_fromlebytes_6",
  ([(*args*)
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("x", "uint8_t[static 48]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "48"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_fromlebytes_p521",
  ([(*args*)
     ("z", "uint64_t[static 9]", (*is const?*)"false");
     ("x", "uint8_t[static 66]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "66"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_ge",
  ([(*args*)
     ("m", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("n", "uint64_t", (*is const?*)"false");
     ("y", "uint64_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "m"(* num elems *), 8(* elem bytesize *));
    ("y", "n"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("bignum_gt",
  ([(*args*)
     ("m", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("n", "uint64_t", (*is const?*)"false");
     ("y", "uint64_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "m"(* num elems *), 8(* elem bytesize *));
    ("y", "n"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("bignum_half_p256",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_half_p256k1",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_half_p384",
  ([(*args*)
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_half_p521",
  ([(*args*)
     ("z", "uint64_t[static 9]", (*is const?*)"false");
     ("x", "uint64_t[static 9]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_half_sm2",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_inv_p25519",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_inv_p256",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_inv_p384",
  ([(*args*)
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_inv_p521",
  ([(*args*)
     ("z", "uint64_t[static 9]", (*is const?*)"false");
     ("x", "uint64_t[static 9]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_inv_sm2",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_invsqrt_p25519",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "int64_t",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_invsqrt_p25519_alt",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "int64_t",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_iszero",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("bignum_kmul_16_32",
  ([(*args*)
     ("z", "uint64_t[static 32]", (*is const?*)"false");
     ("x", "uint64_t[static 16]", (*is const?*)"true");
     ("y", "uint64_t[static 16]", (*is const?*)"true");
     ("t", "uint64_t[static 32]", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("x", "16"(* num elems *), 8(* elem bytesize *));
    ("y", "16"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "32"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
    ("t", ">=32"(* num elems *), 8(* elem bytesize *));
   ])
);

("bignum_kmul_32_64",
  ([(*args*)
     ("z", "uint64_t[static 64]", (*is const?*)"false");
     ("x", "uint64_t[static 32]", (*is const?*)"true");
     ("y", "uint64_t[static 32]", (*is const?*)"true");
     ("t", "uint64_t[static 96]", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("x", "32"(* num elems *), 8(* elem bytesize *));
    ("y", "32"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "64"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
    ("t", ">=96"(* num elems *), 8(* elem bytesize *));
   ])
);

("bignum_ksqr_16_32",
  ([(*args*)
     ("z", "uint64_t[static 32]", (*is const?*)"false");
     ("x", "uint64_t[static 16]", (*is const?*)"true");
     ("t", "uint64_t[static 24]", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("x", "16"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "32"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
    ("t", ">=24"(* num elems *), 8(* elem bytesize *));
   ])
);

("bignum_ksqr_32_64",
  ([(*args*)
     ("z", "uint64_t[static 64]", (*is const?*)"false");
     ("x", "uint64_t[static 32]", (*is const?*)"true");
     ("t", "uint64_t[static 72]", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("x", "32"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "64"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
    ("t", ">=72"(* num elems *), 8(* elem bytesize *));
   ])
);

("bignum_le",
  ([(*args*)
     ("m", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("n", "uint64_t", (*is const?*)"false");
     ("y", "uint64_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "m"(* num elems *), 8(* elem bytesize *));
    ("y", "n"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("bignum_littleendian_4",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_littleendian_6",
  ([(*args*)
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_lt",
  ([(*args*)
     ("m", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("n", "uint64_t", (*is const?*)"false");
     ("y", "uint64_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "m"(* num elems *), 8(* elem bytesize *));
    ("y", "n"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("bignum_madd",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("m", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("n", "uint64_t", (*is const?*)"false");
     ("y", "uint64_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "m"(* num elems *), 8(* elem bytesize *));
    ("y", "n"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_madd_n25519",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
     ("y", "uint64_t[static 4]", (*is const?*)"true");
     ("c", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
    ("y", "4"(* num elems *), 8(* elem bytesize *));
    ("c", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_madd_n25519_alt",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
     ("y", "uint64_t[static 4]", (*is const?*)"true");
     ("c", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
    ("y", "4"(* num elems *), 8(* elem bytesize *));
    ("c", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mod_m25519",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("k", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mod_m25519_4",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mod_n25519",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("k", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mod_n25519_4",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mod_n256",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("k", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mod_n256_4",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mod_n256k1",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("k", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mod_n256k1_4",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mod_n384",
  ([(*args*)
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("k", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mod_n384_6",
  ([(*args*)
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mod_n521_9",
  ([(*args*)
     ("z", "uint64_t[static 9]", (*is const?*)"false");
     ("x", "uint64_t[static 9]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mod_nsm2",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("k", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mod_nsm2_4",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mod_p25519_4",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mod_p256",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("k", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mod_p256_4",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mod_p256k1",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("k", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mod_p256k1_4",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mod_p384",
  ([(*args*)
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("k", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mod_p384_6",
  ([(*args*)
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mod_p521_9",
  ([(*args*)
     ("z", "uint64_t[static 9]", (*is const?*)"false");
     ("x", "uint64_t[static 9]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mod_sm2",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("k", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mod_sm2_4",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_modadd",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("y", "uint64_t*", (*is const?*)"true");
     ("m", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
    ("y", "k"(* num elems *), 8(* elem bytesize *));
    ("m", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_moddouble",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("m", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
    ("m", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_modexp",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("a", "uint64_t*", (*is const?*)"true");
     ("p", "uint64_t*", (*is const?*)"true");
     ("m", "uint64_t*", (*is const?*)"true");
     ("t", "uint64_t*", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("a", "k"(* num elems *), 8(* elem bytesize *));
    ("p", "k"(* num elems *), 8(* elem bytesize *));
    ("m", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
    ("t", ">=3*k"(* num elems *), 8(* elem bytesize *));
   ])
);

("bignum_modifier",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("m", "uint64_t*", (*is const?*)"true");
     ("t", "uint64_t*", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("m", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
    ("t", ">=k"(* num elems *), 8(* elem bytesize *));
   ])
);

("bignum_modinv",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("a", "uint64_t*", (*is const?*)"true");
     ("b", "uint64_t*", (*is const?*)"true");
     ("t", "uint64_t*", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("a", "k"(* num elems *), 8(* elem bytesize *));
    ("b", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
    ("t", ">=3*k"(* num elems *), 8(* elem bytesize *));
   ])
);

("bignum_modoptneg",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("p", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("m", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
    ("m", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_modsub",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("y", "uint64_t*", (*is const?*)"true");
     ("m", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
    ("y", "k"(* num elems *), 8(* elem bytesize *));
    ("m", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montifier",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("m", "uint64_t*", (*is const?*)"true");
     ("t", "uint64_t*", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("m", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
    ("t", ">=k"(* num elems *), 8(* elem bytesize *));
   ])
);

("bignum_montinv_p256",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montinv_p384",
  ([(*args*)
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montinv_sm2",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montmul",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("y", "uint64_t*", (*is const?*)"true");
     ("m", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
    ("y", "k"(* num elems *), 8(* elem bytesize *));
    ("m", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montmul_p256",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
     ("y", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
    ("y", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montmul_p256_alt",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
     ("y", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
    ("y", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montmul_p256k1",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
     ("y", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
    ("y", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montmul_p256k1_alt",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
     ("y", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
    ("y", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montmul_p384",
  ([(*args*)
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
     ("y", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
    ("y", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montmul_p384_alt",
  ([(*args*)
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
     ("y", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
    ("y", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montmul_p521",
  ([(*args*)
     ("z", "uint64_t[static 9]", (*is const?*)"false");
     ("x", "uint64_t[static 9]", (*is const?*)"true");
     ("y", "uint64_t[static 9]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "9"(* num elems *), 8(* elem bytesize *));
    ("y", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montmul_p521_alt",
  ([(*args*)
     ("z", "uint64_t[static 9]", (*is const?*)"false");
     ("x", "uint64_t[static 9]", (*is const?*)"true");
     ("y", "uint64_t[static 9]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "9"(* num elems *), 8(* elem bytesize *));
    ("y", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montmul_sm2",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
     ("y", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
    ("y", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montmul_sm2_alt",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
     ("y", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
    ("y", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montredc",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("n", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("m", "uint64_t*", (*is const?*)"true");
     ("p", "uint64_t", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("x", "n"(* num elems *), 8(* elem bytesize *));
    ("m", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montsqr",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("m", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
    ("m", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montsqr_p256",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montsqr_p256_alt",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montsqr_p256k1",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montsqr_p256k1_alt",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montsqr_p384",
  ([(*args*)
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montsqr_p384_alt",
  ([(*args*)
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montsqr_p521",
  ([(*args*)
     ("z", "uint64_t[static 9]", (*is const?*)"false");
     ("x", "uint64_t[static 9]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montsqr_p521_alt",
  ([(*args*)
     ("z", "uint64_t[static 9]", (*is const?*)"false");
     ("x", "uint64_t[static 9]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montsqr_sm2",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_montsqr_sm2_alt",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mul",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("m", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("n", "uint64_t", (*is const?*)"false");
     ("y", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "m"(* num elems *), 8(* elem bytesize *));
    ("y", "n"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mul_4_8",
  ([(*args*)
     ("z", "uint64_t[static 8]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
     ("y", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
    ("y", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mul_4_8_alt",
  ([(*args*)
     ("z", "uint64_t[static 8]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
     ("y", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
    ("y", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mul_6_12",
  ([(*args*)
     ("z", "uint64_t[static 12]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
     ("y", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
    ("y", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mul_6_12_alt",
  ([(*args*)
     ("z", "uint64_t[static 12]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
     ("y", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
    ("y", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mul_8_16",
  ([(*args*)
     ("z", "uint64_t[static 16]", (*is const?*)"false");
     ("x", "uint64_t[static 8]", (*is const?*)"true");
     ("y", "uint64_t[static 8]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "8"(* num elems *), 8(* elem bytesize *));
    ("y", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "16"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mul_8_16_alt",
  ([(*args*)
     ("z", "uint64_t[static 16]", (*is const?*)"false");
     ("x", "uint64_t[static 8]", (*is const?*)"true");
     ("y", "uint64_t[static 8]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "8"(* num elems *), 8(* elem bytesize *));
    ("y", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "16"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mul_p25519",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
     ("y", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
    ("y", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mul_p25519_alt",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
     ("y", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
    ("y", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mul_p256k1",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
     ("y", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
    ("y", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mul_p256k1_alt",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
     ("y", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
    ("y", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mul_p521",
  ([(*args*)
     ("z", "uint64_t[static 9]", (*is const?*)"false");
     ("x", "uint64_t[static 9]", (*is const?*)"true");
     ("y", "uint64_t[static 9]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "9"(* num elems *), 8(* elem bytesize *));
    ("y", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mul_p521_alt",
  ([(*args*)
     ("z", "uint64_t[static 9]", (*is const?*)"false");
     ("x", "uint64_t[static 9]", (*is const?*)"true");
     ("y", "uint64_t[static 9]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "9"(* num elems *), 8(* elem bytesize *));
    ("y", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_muladd10",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("d", "uint64_t", (*is const?*)"false");
   ],
   "uint64_t",
   [(* input buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mux",
  ([(*args*)
     ("p", "uint64_t", (*is const?*)"false");
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("y", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
    ("y", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mux16",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("xs", "uint64_t*", (*is const?*)"true");
     ("i", "uint64_t", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("xs", "16*k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mux_4",
  ([(*args*)
     ("p", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
     ("y", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
    ("y", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_mux_6",
  ([(*args*)
     ("p", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
     ("y", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
    ("y", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_neg_p25519",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_neg_p256",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_neg_p256k1",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_neg_p384",
  ([(*args*)
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_neg_p521",
  ([(*args*)
     ("z", "uint64_t[static 9]", (*is const?*)"false");
     ("x", "uint64_t[static 9]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_neg_sm2",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_negmodinv",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_nonzero",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("bignum_nonzero_4",
  ([(*args*)
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("bignum_nonzero_6",
  ([(*args*)
     ("x", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("bignum_normalize",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
   ],
   "uint64_t",
   [(* input buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_odd",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("bignum_of_word",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("n", "uint64_t", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_optadd",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("p", "uint64_t", (*is const?*)"false");
     ("y", "uint64_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
    ("y", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_optneg",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("p", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_optneg_p25519",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("p", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_optneg_p256",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("p", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_optneg_p256k1",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("p", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_optneg_p384",
  ([(*args*)
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("p", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_optneg_p521",
  ([(*args*)
     ("z", "uint64_t[static 9]", (*is const?*)"false");
     ("p", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t[static 9]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_optneg_sm2",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("p", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_optsub",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("p", "uint64_t", (*is const?*)"false");
     ("y", "uint64_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
    ("y", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_optsubadd",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("p", "uint64_t", (*is const?*)"false");
     ("y", "uint64_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "k"(* num elems *), 8(* elem bytesize *));
    ("y", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_pow2",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("n", "uint64_t", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_shl_small",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("n", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("c", "uint64_t", (*is const?*)"false");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "n"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_shr_small",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("n", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("c", "uint64_t", (*is const?*)"false");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "n"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_sqr",
  ([(*args*)
     ("k", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("n", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "n"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "k"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_sqr_4_8",
  ([(*args*)
     ("z", "uint64_t[static 8]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_sqr_4_8_alt",
  ([(*args*)
     ("z", "uint64_t[static 8]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_sqr_6_12",
  ([(*args*)
     ("z", "uint64_t[static 12]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_sqr_6_12_alt",
  ([(*args*)
     ("z", "uint64_t[static 12]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_sqr_8_16",
  ([(*args*)
     ("z", "uint64_t[static 16]", (*is const?*)"false");
     ("x", "uint64_t[static 8]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "16"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_sqr_8_16_alt",
  ([(*args*)
     ("z", "uint64_t[static 16]", (*is const?*)"false");
     ("x", "uint64_t[static 8]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "16"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_sqr_p25519",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_sqr_p25519_alt",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_sqr_p256k1",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_sqr_p256k1_alt",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_sqr_p521",
  ([(*args*)
     ("z", "uint64_t[static 9]", (*is const?*)"false");
     ("x", "uint64_t[static 9]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_sqr_p521_alt",
  ([(*args*)
     ("z", "uint64_t[static 9]", (*is const?*)"false");
     ("x", "uint64_t[static 9]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_sqrt_p25519",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "int64_t",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_sqrt_p25519_alt",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "int64_t",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_sub",
  ([(*args*)
     ("p", "uint64_t", (*is const?*)"false");
     ("z", "uint64_t*", (*is const?*)"false");
     ("m", "uint64_t", (*is const?*)"false");
     ("x", "uint64_t*", (*is const?*)"true");
     ("n", "uint64_t", (*is const?*)"false");
     ("y", "uint64_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("x", "m"(* num elems *), 8(* elem bytesize *));
    ("y", "n"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "p"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_sub_p25519",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
     ("y", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
    ("y", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_sub_p256",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
     ("y", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
    ("y", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_sub_p256k1",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
     ("y", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
    ("y", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_sub_p384",
  ([(*args*)
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
     ("y", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
    ("y", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_sub_p521",
  ([(*args*)
     ("z", "uint64_t[static 9]", (*is const?*)"false");
     ("x", "uint64_t[static 9]", (*is const?*)"true");
     ("y", "uint64_t[static 9]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "9"(* num elems *), 8(* elem bytesize *));
    ("y", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_sub_sm2",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
     ("y", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
    ("y", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_tobebytes_4",
  ([(*args*)
     ("z", "uint8_t[static 32]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "32"(* num elems *), 1(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_tobebytes_6",
  ([(*args*)
     ("z", "uint8_t[static 48]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "48"(* num elems *), 1(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_tolebytes_4",
  ([(*args*)
     ("z", "uint8_t[static 32]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "32"(* num elems *), 1(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_tolebytes_6",
  ([(*args*)
     ("z", "uint8_t[static 48]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "48"(* num elems *), 1(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_tolebytes_p521",
  ([(*args*)
     ("z", "uint8_t[static 66]", (*is const?*)"false");
     ("x", "uint64_t[static 9]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "66"(* num elems *), 1(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_tomont_p256",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_tomont_p256k1",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_tomont_p384",
  ([(*args*)
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_tomont_p521",
  ([(*args*)
     ("z", "uint64_t[static 9]", (*is const?*)"false");
     ("x", "uint64_t[static 9]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_tomont_sm2",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_triple_p256",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_triple_p256k1",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_triple_p384",
  ([(*args*)
     ("z", "uint64_t[static 6]", (*is const?*)"false");
     ("x", "uint64_t[static 6]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "6"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_triple_p521",
  ([(*args*)
     ("z", "uint64_t[static 9]", (*is const?*)"false");
     ("x", "uint64_t[static 9]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "9"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("bignum_triple_sm2",
  ([(*args*)
     ("z", "uint64_t[static 4]", (*is const?*)"false");
     ("x", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("x", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("curve25519_ladderstep",
  ([(*args*)
     ("rr", "uint64_t[16]", (*is const?*)"false");
     ("point", "uint64_t[8]", (*is const?*)"true");
     ("pp", "uint64_t[16]", (*is const?*)"true");
     ("b", "uint64_t", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("point", "8"(* num elems *), 8(* elem bytesize *));
    ("pp", "16"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("rr", "16"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("curve25519_ladderstep_alt",
  ([(*args*)
     ("rr", "uint64_t[16]", (*is const?*)"false");
     ("point", "uint64_t[8]", (*is const?*)"true");
     ("pp", "uint64_t[16]", (*is const?*)"true");
     ("b", "uint64_t", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("point", "8"(* num elems *), 8(* elem bytesize *));
    ("pp", "16"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("rr", "16"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("curve25519_pxscalarmul",
  ([(*args*)
     ("res", "uint64_t[static 8]", (*is const?*)"false");
     ("scalar", "uint64_t[static 4]", (*is const?*)"true");
     ("point", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "4"(* num elems *), 8(* elem bytesize *));
    ("point", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("curve25519_pxscalarmul_alt",
  ([(*args*)
     ("res", "uint64_t[static 8]", (*is const?*)"false");
     ("scalar", "uint64_t[static 4]", (*is const?*)"true");
     ("point", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "4"(* num elems *), 8(* elem bytesize *));
    ("point", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("curve25519_x25519",
  ([(*args*)
     ("res", "uint64_t[static 4]", (*is const?*)"false");
     ("scalar", "uint64_t[static 4]", (*is const?*)"true");
     ("point", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "4"(* num elems *), 8(* elem bytesize *));
    ("point", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("curve25519_x25519_alt",
  ([(*args*)
     ("res", "uint64_t[static 4]", (*is const?*)"false");
     ("scalar", "uint64_t[static 4]", (*is const?*)"true");
     ("point", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "4"(* num elems *), 8(* elem bytesize *));
    ("point", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("curve25519_x25519_byte",
  ([(*args*)
     ("res", "uint8_t[static 32]", (*is const?*)"false");
     ("scalar", "uint8_t[static 32]", (*is const?*)"true");
     ("point", "uint8_t[static 32]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "32"(* num elems *), 1(* elem bytesize *));
    ("point", "32"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "32"(* num elems *), 1(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("curve25519_x25519_byte_alt",
  ([(*args*)
     ("res", "uint8_t[static 32]", (*is const?*)"false");
     ("scalar", "uint8_t[static 32]", (*is const?*)"true");
     ("point", "uint8_t[static 32]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "32"(* num elems *), 1(* elem bytesize *));
    ("point", "32"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "32"(* num elems *), 1(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("curve25519_x25519base",
  ([(*args*)
     ("res", "uint64_t[static 4]", (*is const?*)"false");
     ("scalar", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("curve25519_x25519base_alt",
  ([(*args*)
     ("res", "uint64_t[static 4]", (*is const?*)"false");
     ("scalar", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("curve25519_x25519base_byte",
  ([(*args*)
     ("res", "uint8_t[static 32]", (*is const?*)"false");
     ("scalar", "uint8_t[static 32]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "32"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "32"(* num elems *), 1(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("curve25519_x25519base_byte_alt",
  ([(*args*)
     ("res", "uint8_t[static 32]", (*is const?*)"false");
     ("scalar", "uint8_t[static 32]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "32"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "32"(* num elems *), 1(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("edwards25519_decode",
  ([(*args*)
     ("z", "uint64_t[static 8]", (*is const?*)"false");
     ("c", "uint8_t[static 32]", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("c", "32"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("edwards25519_decode_alt",
  ([(*args*)
     ("z", "uint64_t[static 8]", (*is const?*)"false");
     ("c", "uint8_t[static 32]", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("c", "32"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("edwards25519_encode",
  ([(*args*)
     ("z", "uint8_t[static 32]", (*is const?*)"false");
     ("p", "uint64_t[static 8]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("z", "32"(* num elems *), 1(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("edwards25519_epadd",
  ([(*args*)
     ("p3", "uint64_t[static 16]", (*is const?*)"false");
     ("p1", "uint64_t[static 16]", (*is const?*)"true");
     ("p2", "uint64_t[static 16]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "16"(* num elems *), 8(* elem bytesize *));
    ("p2", "16"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "16"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("edwards25519_epadd_alt",
  ([(*args*)
     ("p3", "uint64_t[static 16]", (*is const?*)"false");
     ("p1", "uint64_t[static 16]", (*is const?*)"true");
     ("p2", "uint64_t[static 16]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "16"(* num elems *), 8(* elem bytesize *));
    ("p2", "16"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "16"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("edwards25519_epdouble",
  ([(*args*)
     ("p3", "uint64_t[static 16]", (*is const?*)"false");
     ("p1", "uint64_t[static 12]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "16"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("edwards25519_epdouble_alt",
  ([(*args*)
     ("p3", "uint64_t[static 16]", (*is const?*)"false");
     ("p1", "uint64_t[static 12]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "16"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("edwards25519_pdouble",
  ([(*args*)
     ("p3", "uint64_t[static 12]", (*is const?*)"false");
     ("p1", "uint64_t[static 12]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("edwards25519_pdouble_alt",
  ([(*args*)
     ("p3", "uint64_t[static 12]", (*is const?*)"false");
     ("p1", "uint64_t[static 12]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("edwards25519_pepadd",
  ([(*args*)
     ("p3", "uint64_t[static 16]", (*is const?*)"false");
     ("p1", "uint64_t[static 16]", (*is const?*)"true");
     ("p2", "uint64_t[static 12]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "16"(* num elems *), 8(* elem bytesize *));
    ("p2", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "16"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("edwards25519_pepadd_alt",
  ([(*args*)
     ("p3", "uint64_t[static 16]", (*is const?*)"false");
     ("p1", "uint64_t[static 16]", (*is const?*)"true");
     ("p2", "uint64_t[static 12]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "16"(* num elems *), 8(* elem bytesize *));
    ("p2", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "16"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("edwards25519_scalarmulbase",
  ([(*args*)
     ("res", "uint64_t[static 8]", (*is const?*)"false");
     ("scalar", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("edwards25519_scalarmulbase_alt",
  ([(*args*)
     ("res", "uint64_t[static 8]", (*is const?*)"false");
     ("scalar", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("edwards25519_scalarmuldouble",
  ([(*args*)
     ("res", "uint64_t[static 8]", (*is const?*)"false");
     ("scalar", "uint64_t[static 4]", (*is const?*)"true");
     ("point", "uint64_t[static 8]", (*is const?*)"true");
     ("bscalar", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "4"(* num elems *), 8(* elem bytesize *));
    ("point", "8"(* num elems *), 8(* elem bytesize *));
    ("bscalar", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("edwards25519_scalarmuldouble_alt",
  ([(*args*)
     ("res", "uint64_t[static 8]", (*is const?*)"false");
     ("scalar", "uint64_t[static 4]", (*is const?*)"true");
     ("point", "uint64_t[static 8]", (*is const?*)"true");
     ("bscalar", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "4"(* num elems *), 8(* elem bytesize *));
    ("point", "8"(* num elems *), 8(* elem bytesize *));
    ("bscalar", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mldsa_caddq",
  ([(*args*)
     ("a", "int32_t[static 256]", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 4(* elem bytesize *));
   ],
   [(* output buffers *)
    ("a", "256"(* num elems *), 4(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mldsa_chknorm",
  ([(*args*)
     ("a", "int32_t[static 256]", (*is const?*)"true");
     ("bound", "uint64_t", (*is const?*)"false");
   ],
   "uint64_t",
   [(* input buffers *)
    ("a", "256"(* num elems *), 4(* elem bytesize *));
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("mldsa_decompose_32",
  ([(*args*)
     ("a1", "int32_t[static 256]", (*is const?*)"false");
     ("a0", "int32_t[static 256]", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("a0", "256"(* num elems *), 4(* elem bytesize *));
   ],
   [(* output buffers *)
    ("a1", "256"(* num elems *), 4(* elem bytesize *));
    ("a0", "256"(* num elems *), 4(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mldsa_decompose_88",
  ([(*args*)
     ("a1", "int32_t[static 256]", (*is const?*)"false");
     ("a0", "int32_t[static 256]", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("a0", "256"(* num elems *), 4(* elem bytesize *));
   ],
   [(* output buffers *)
    ("a1", "256"(* num elems *), 4(* elem bytesize *));
    ("a0", "256"(* num elems *), 4(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mldsa_intt_arm",
  ([(*args*)
     ("a", "int32_t[static 256]", (*is const?*)"false");
     ("z_78", "int32_t[static 384]", (*is const?*)"true");
     ("z_123456", "int32_t[static 160]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 4(* elem bytesize *));
    ("z_78", "384"(* num elems *), 4(* elem bytesize *));
    ("z_123456", "160"(* num elems *), 4(* elem bytesize *));
   ],
   [(* output buffers *)
    ("a", "256"(* num elems *), 4(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mldsa_ntt_arm",
  ([(*args*)
     ("a", "int32_t[static 256]", (*is const?*)"false");
     ("z_012345", "int32_t[144]", (*is const?*)"true");
     ("z_67", "int32_t[384]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 4(* elem bytesize *));
    ("z_012345", "144"(* num elems *), 4(* elem bytesize *));
    ("z_67", "384"(* num elems *), 4(* elem bytesize *));
   ],
   [(* output buffers *)
    ("a", "256"(* num elems *), 4(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mldsa_pointwise",
  ([(*args*)
     ("r", "int32_t[static 256]", (*is const?*)"false");
     ("a", "int32_t[static 256]", (*is const?*)"true");
     ("b", "int32_t[static 256]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 4(* elem bytesize *));
    ("b", "256"(* num elems *), 4(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "256"(* num elems *), 4(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mldsa_pointwise_acc_l4",
  ([(*args*)
     ("r", "int32_t[static 256]", (*is const?*)"false");
     ("a", "int32_t[static 1024]", (*is const?*)"true");
     ("b", "int32_t[static 1024]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "1024"(* num elems *), 4(* elem bytesize *));
    ("b", "1024"(* num elems *), 4(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "256"(* num elems *), 4(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mldsa_pointwise_acc_l5",
  ([(*args*)
     ("r", "int32_t[static 256]", (*is const?*)"false");
     ("a", "int32_t[static 1280]", (*is const?*)"true");
     ("b", "int32_t[static 1280]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "1280"(* num elems *), 4(* elem bytesize *));
    ("b", "1280"(* num elems *), 4(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "256"(* num elems *), 4(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mldsa_pointwise_acc_l7",
  ([(*args*)
     ("r", "int32_t[static 256]", (*is const?*)"false");
     ("a", "int32_t[static 1792]", (*is const?*)"true");
     ("b", "int32_t[static 1792]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "1792"(* num elems *), 4(* elem bytesize *));
    ("b", "1792"(* num elems *), 4(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "256"(* num elems *), 4(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mldsa_poly_use_hint_32",
  ([(*args*)
     ("b", "int32_t[static 256]", (*is const?*)"false");
     ("a", "int32_t[static 256]", (*is const?*)"true");
     ("h", "int32_t[static 256]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 4(* elem bytesize *));
    ("h", "256"(* num elems *), 4(* elem bytesize *));
   ],
   [(* output buffers *)
    ("b", "256"(* num elems *), 4(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mldsa_poly_use_hint_88",
  ([(*args*)
     ("b", "int32_t[static 256]", (*is const?*)"false");
     ("a", "int32_t[static 256]", (*is const?*)"true");
     ("h", "int32_t[static 256]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 4(* elem bytesize *));
    ("h", "256"(* num elems *), 4(* elem bytesize *));
   ],
   [(* output buffers *)
    ("b", "256"(* num elems *), 4(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mldsa_polyz_unpack_17_arm",
  ([(*args*)
     ("r", "int32_t[static 256]", (*is const?*)"false");
     ("b", "uint8_t[static 576]", (*is const?*)"true");
     ("t", "uint8_t[static 64]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("b", "576"(* num elems *), 1(* elem bytesize *));
    ("t", "64"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "256"(* num elems *), 4(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mldsa_polyz_unpack_19_arm",
  ([(*args*)
     ("r", "int32_t[static 256]", (*is const?*)"false");
     ("b", "uint8_t[static 640]", (*is const?*)"true");
     ("t", "uint8_t[static 64]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("b", "640"(* num elems *), 1(* elem bytesize *));
    ("t", "64"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "256"(* num elems *), 4(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mldsa_rej_uniform_VARIABLE_TIME",
  ([(*args*)
     ("r", "int32_t[static 256]", (*is const?*)"false");
     ("buf", "uint8_t*", (*is const?*)"true");
     ("buflen", "uint64_t", (*is const?*)"false");
     ("table", "uint8_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
   ],
   [(* output buffers *)
    ("r", "256"(* num elems *), 4(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mldsa_rej_uniform_eta2_VARIABLE_TIME",
  ([(*args*)
     ("r", "int32_t[static 256]", (*is const?*)"false");
     ("buf", "uint8_t*", (*is const?*)"true");
     ("buflen", "unsigned", (*is const?*)"false");
     ("table", "uint8_t[static 4096]", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("buf", "buflen"(* num elems *), 1(* elem bytesize *));
    ("table", "4096"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "256"(* num elems *), 4(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mldsa_rej_uniform_eta4_VARIABLE_TIME",
  ([(*args*)
     ("r", "int32_t[static 256]", (*is const?*)"false");
     ("buf", "uint8_t*", (*is const?*)"true");
     ("buflen", "unsigned", (*is const?*)"false");
     ("table", "uint8_t[static 4096]", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
    ("buf", "buflen"(* num elems *), 1(* elem bytesize *));
    ("table", "4096"(* num elems *), 1(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "256"(* num elems *), 4(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_basemul_k2",
  ([(*args*)
     ("r", "int16_t[static 256]", (*is const?*)"false");
     ("a", "int16_t[static 512]", (*is const?*)"true");
     ("b", "int16_t[static 512]", (*is const?*)"true");
     ("bt", "int16_t[static 256]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "512"(* num elems *), 2(* elem bytesize *));
    ("b", "512"(* num elems *), 2(* elem bytesize *));
    ("bt", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_basemul_k3",
  ([(*args*)
     ("r", "int16_t[static 256]", (*is const?*)"false");
     ("a", "int16_t[static 768]", (*is const?*)"true");
     ("b", "int16_t[static 768]", (*is const?*)"true");
     ("bt", "int16_t[static 384]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "768"(* num elems *), 2(* elem bytesize *));
    ("b", "768"(* num elems *), 2(* elem bytesize *));
    ("bt", "384"(* num elems *), 2(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_basemul_k4",
  ([(*args*)
     ("r", "int16_t[static 256]", (*is const?*)"false");
     ("a", "int16_t[static 1024]", (*is const?*)"true");
     ("b", "int16_t[static 1024]", (*is const?*)"true");
     ("bt", "int16_t[static 512]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "1024"(* num elems *), 2(* elem bytesize *));
    ("b", "1024"(* num elems *), 2(* elem bytesize *));
    ("bt", "512"(* num elems *), 2(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_intt",
  ([(*args*)
     ("a", "int16_t[static 256]", (*is const?*)"false");
     ("z_01234", "int16_t[static 80]", (*is const?*)"true");
     ("z_56", "int16_t[static 384]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
    ("z_01234", "80"(* num elems *), 2(* elem bytesize *));
    ("z_56", "384"(* num elems *), 2(* elem bytesize *));
   ],
   [(* output buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_mulcache_compute",
  ([(*args*)
     ("x", "int16_t[static 128]", (*is const?*)"false");
     ("a", "int16_t[static 256]", (*is const?*)"true");
     ("z", "int16_t[static 128]", (*is const?*)"true");
     ("t", "int16_t[static 128]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
    ("z", "128"(* num elems *), 2(* elem bytesize *));
    ("t", "128"(* num elems *), 2(* elem bytesize *));
   ],
   [(* output buffers *)
    ("x", "128"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_ntt",
  ([(*args*)
     ("a", "int16_t[static 256]", (*is const?*)"false");
     ("z_01234", "int16_t[static 80]", (*is const?*)"true");
     ("z_56", "int16_t[static 384]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
    ("z_01234", "80"(* num elems *), 2(* elem bytesize *));
    ("z_56", "384"(* num elems *), 2(* elem bytesize *));
   ],
   [(* output buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_reduce",
  ([(*args*)
     ("a", "int16_t[static 256]", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* output buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_rej_uniform_VARIABLE_TIME",
  ([(*args*)
     ("r", "int16_t[static 256]", (*is const?*)"false");
     ("buf", "uint8_t*", (*is const?*)"true");
     ("buflen", "uint64_t", (*is const?*)"false");
     ("table", "uint8_t*", (*is const?*)"true");
   ],
   "uint64_t",
   [(* input buffers *)
   ],
   [(* output buffers *)
    ("r", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_tobytes",
  ([(*args*)
     ("r", "uint8_t[static 384]", (*is const?*)"false");
     ("a", "int16_t[static 256]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* output buffers *)
    ("r", "384"(* num elems *), 1(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("mlkem_tomont",
  ([(*args*)
     ("a", "int16_t[static 256]", (*is const?*)"false");
   ],
   "void",
   [(* input buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* output buffers *)
    ("a", "256"(* num elems *), 2(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p256_montjadd",
  ([(*args*)
     ("p3", "uint64_t[static 12]", (*is const?*)"false");
     ("p1", "uint64_t[static 12]", (*is const?*)"true");
     ("p2", "uint64_t[static 12]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "12"(* num elems *), 8(* elem bytesize *));
    ("p2", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p256_montjadd_alt",
  ([(*args*)
     ("p3", "uint64_t[static 12]", (*is const?*)"false");
     ("p1", "uint64_t[static 12]", (*is const?*)"true");
     ("p2", "uint64_t[static 12]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "12"(* num elems *), 8(* elem bytesize *));
    ("p2", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p256_montjdouble",
  ([(*args*)
     ("p3", "uint64_t[static 12]", (*is const?*)"false");
     ("p1", "uint64_t[static 12]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p256_montjdouble_alt",
  ([(*args*)
     ("p3", "uint64_t[static 12]", (*is const?*)"false");
     ("p1", "uint64_t[static 12]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p256_montjmixadd",
  ([(*args*)
     ("p3", "uint64_t[static 12]", (*is const?*)"false");
     ("p1", "uint64_t[static 12]", (*is const?*)"true");
     ("p2", "uint64_t[static 8]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "12"(* num elems *), 8(* elem bytesize *));
    ("p2", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p256_montjmixadd_alt",
  ([(*args*)
     ("p3", "uint64_t[static 12]", (*is const?*)"false");
     ("p1", "uint64_t[static 12]", (*is const?*)"true");
     ("p2", "uint64_t[static 8]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "12"(* num elems *), 8(* elem bytesize *));
    ("p2", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p256_montjscalarmul",
  ([(*args*)
     ("res", "uint64_t[static 12]", (*is const?*)"false");
     ("scalar", "uint64_t[static 4]", (*is const?*)"true");
     ("point", "uint64_t[static 12]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "4"(* num elems *), 8(* elem bytesize *));
    ("point", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p256_montjscalarmul_alt",
  ([(*args*)
     ("res", "uint64_t[static 12]", (*is const?*)"false");
     ("scalar", "uint64_t[static 4]", (*is const?*)"true");
     ("point", "uint64_t[static 12]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "4"(* num elems *), 8(* elem bytesize *));
    ("point", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p256_scalarmul",
  ([(*args*)
     ("res", "uint64_t[static 8]", (*is const?*)"false");
     ("scalar", "uint64_t[static 4]", (*is const?*)"true");
     ("point", "uint64_t[static 8]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "4"(* num elems *), 8(* elem bytesize *));
    ("point", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p256_scalarmul_alt",
  ([(*args*)
     ("res", "uint64_t[static 8]", (*is const?*)"false");
     ("scalar", "uint64_t[static 4]", (*is const?*)"true");
     ("point", "uint64_t[static 8]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "4"(* num elems *), 8(* elem bytesize *));
    ("point", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p256_scalarmulbase",
  ([(*args*)
     ("res", "uint64_t[static 8]", (*is const?*)"false");
     ("scalar", "uint64_t[static 4]", (*is const?*)"true");
     ("blocksize", "uint64_t", (*is const?*)"false");
     ("table", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "4"(* num elems *), 8(* elem bytesize *));
    ("table", ""(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p256_scalarmulbase_alt",
  ([(*args*)
     ("res", "uint64_t[static 8]", (*is const?*)"false");
     ("scalar", "uint64_t[static 4]", (*is const?*)"true");
     ("blocksize", "uint64_t", (*is const?*)"false");
     ("table", "uint64_t*", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "4"(* num elems *), 8(* elem bytesize *));
    ("table", ""(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p384_montjadd",
  ([(*args*)
     ("p3", "uint64_t[static 18]", (*is const?*)"false");
     ("p1", "uint64_t[static 18]", (*is const?*)"true");
     ("p2", "uint64_t[static 18]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "18"(* num elems *), 8(* elem bytesize *));
    ("p2", "18"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "18"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p384_montjadd_alt",
  ([(*args*)
     ("p3", "uint64_t[static 18]", (*is const?*)"false");
     ("p1", "uint64_t[static 18]", (*is const?*)"true");
     ("p2", "uint64_t[static 18]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "18"(* num elems *), 8(* elem bytesize *));
    ("p2", "18"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "18"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p384_montjdouble",
  ([(*args*)
     ("p3", "uint64_t[static 18]", (*is const?*)"false");
     ("p1", "uint64_t[static 18]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "18"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "18"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p384_montjdouble_alt",
  ([(*args*)
     ("p3", "uint64_t[static 18]", (*is const?*)"false");
     ("p1", "uint64_t[static 18]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "18"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "18"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p384_montjmixadd",
  ([(*args*)
     ("p3", "uint64_t[static 18]", (*is const?*)"false");
     ("p1", "uint64_t[static 18]", (*is const?*)"true");
     ("p2", "uint64_t[static 12]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "18"(* num elems *), 8(* elem bytesize *));
    ("p2", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "18"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p384_montjmixadd_alt",
  ([(*args*)
     ("p3", "uint64_t[static 18]", (*is const?*)"false");
     ("p1", "uint64_t[static 18]", (*is const?*)"true");
     ("p2", "uint64_t[static 12]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "18"(* num elems *), 8(* elem bytesize *));
    ("p2", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "18"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p384_montjscalarmul",
  ([(*args*)
     ("res", "uint64_t[static 18]", (*is const?*)"false");
     ("scalar", "uint64_t[static 6]", (*is const?*)"true");
     ("point", "uint64_t[static 18]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "6"(* num elems *), 8(* elem bytesize *));
    ("point", "18"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "18"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p384_montjscalarmul_alt",
  ([(*args*)
     ("res", "uint64_t[static 18]", (*is const?*)"false");
     ("scalar", "uint64_t[static 6]", (*is const?*)"true");
     ("point", "uint64_t[static 18]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "6"(* num elems *), 8(* elem bytesize *));
    ("point", "18"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "18"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p521_jadd",
  ([(*args*)
     ("p3", "uint64_t[static 27]", (*is const?*)"false");
     ("p1", "uint64_t[static 27]", (*is const?*)"true");
     ("p2", "uint64_t[static 27]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "27"(* num elems *), 8(* elem bytesize *));
    ("p2", "27"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "27"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p521_jadd_alt",
  ([(*args*)
     ("p3", "uint64_t[static 27]", (*is const?*)"false");
     ("p1", "uint64_t[static 27]", (*is const?*)"true");
     ("p2", "uint64_t[static 27]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "27"(* num elems *), 8(* elem bytesize *));
    ("p2", "27"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "27"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p521_jdouble",
  ([(*args*)
     ("p3", "uint64_t[static 27]", (*is const?*)"false");
     ("p1", "uint64_t[static 27]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "27"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "27"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p521_jdouble_alt",
  ([(*args*)
     ("p3", "uint64_t[static 27]", (*is const?*)"false");
     ("p1", "uint64_t[static 27]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "27"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "27"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p521_jmixadd",
  ([(*args*)
     ("p3", "uint64_t[static 27]", (*is const?*)"false");
     ("p1", "uint64_t[static 27]", (*is const?*)"true");
     ("p2", "uint64_t[static 18]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "27"(* num elems *), 8(* elem bytesize *));
    ("p2", "18"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "27"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p521_jmixadd_alt",
  ([(*args*)
     ("p3", "uint64_t[static 27]", (*is const?*)"false");
     ("p1", "uint64_t[static 27]", (*is const?*)"true");
     ("p2", "uint64_t[static 18]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "27"(* num elems *), 8(* elem bytesize *));
    ("p2", "18"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "27"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p521_jscalarmul",
  ([(*args*)
     ("res", "uint64_t[static 27]", (*is const?*)"false");
     ("scalar", "uint64_t[static 9]", (*is const?*)"true");
     ("point", "uint64_t[static 27]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "9"(* num elems *), 8(* elem bytesize *));
    ("point", "27"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "27"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("p521_jscalarmul_alt",
  ([(*args*)
     ("res", "uint64_t[static 27]", (*is const?*)"false");
     ("scalar", "uint64_t[static 9]", (*is const?*)"true");
     ("point", "uint64_t[static 27]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "9"(* num elems *), 8(* elem bytesize *));
    ("point", "27"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "27"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("secp256k1_jadd",
  ([(*args*)
     ("p3", "uint64_t[static 12]", (*is const?*)"false");
     ("p1", "uint64_t[static 12]", (*is const?*)"true");
     ("p2", "uint64_t[static 12]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "12"(* num elems *), 8(* elem bytesize *));
    ("p2", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("secp256k1_jadd_alt",
  ([(*args*)
     ("p3", "uint64_t[static 12]", (*is const?*)"false");
     ("p1", "uint64_t[static 12]", (*is const?*)"true");
     ("p2", "uint64_t[static 12]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "12"(* num elems *), 8(* elem bytesize *));
    ("p2", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("secp256k1_jdouble",
  ([(*args*)
     ("p3", "uint64_t[static 12]", (*is const?*)"false");
     ("p1", "uint64_t[static 12]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("secp256k1_jdouble_alt",
  ([(*args*)
     ("p3", "uint64_t[static 12]", (*is const?*)"false");
     ("p1", "uint64_t[static 12]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("secp256k1_jmixadd",
  ([(*args*)
     ("p3", "uint64_t[static 12]", (*is const?*)"false");
     ("p1", "uint64_t[static 12]", (*is const?*)"true");
     ("p2", "uint64_t[static 8]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "12"(* num elems *), 8(* elem bytesize *));
    ("p2", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("secp256k1_jmixadd_alt",
  ([(*args*)
     ("p3", "uint64_t[static 12]", (*is const?*)"false");
     ("p1", "uint64_t[static 12]", (*is const?*)"true");
     ("p2", "uint64_t[static 8]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "12"(* num elems *), 8(* elem bytesize *));
    ("p2", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("sha3_keccak2_f1600",
  ([(*args*)
     ("a", "uint64_t[static 50]", (*is const?*)"false");
     ("rc", "uint64_t[static 24]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "50"(* num elems *), 8(* elem bytesize *));
    ("rc", "24"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("a", "50"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("sha3_keccak2_f1600_alt",
  ([(*args*)
     ("a", "uint64_t[static 50]", (*is const?*)"false");
     ("rc", "uint64_t[static 24]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "50"(* num elems *), 8(* elem bytesize *));
    ("rc", "24"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("a", "50"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("sha3_keccak4_f1600",
  ([(*args*)
     ("a", "uint64_t[static 100]", (*is const?*)"false");
     ("rc", "uint64_t[static 24]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "100"(* num elems *), 8(* elem bytesize *));
    ("rc", "24"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("a", "100"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("sha3_keccak4_f1600_alt",
  ([(*args*)
     ("a", "uint64_t[static 100]", (*is const?*)"false");
     ("rc", "uint64_t[static 24]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "100"(* num elems *), 8(* elem bytesize *));
    ("rc", "24"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("a", "100"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("sha3_keccak4_f1600_alt2",
  ([(*args*)
     ("a", "uint64_t[static 100]", (*is const?*)"false");
     ("rc", "uint64_t[static 24]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "100"(* num elems *), 8(* elem bytesize *));
    ("rc", "24"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("a", "100"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("sha3_keccak_f1600",
  ([(*args*)
     ("a", "uint64_t[static 25]", (*is const?*)"false");
     ("rc", "uint64_t[static 24]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "25"(* num elems *), 8(* elem bytesize *));
    ("rc", "24"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("a", "25"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("sha3_keccak_f1600_alt",
  ([(*args*)
     ("a", "uint64_t[static 25]", (*is const?*)"false");
     ("rc", "uint64_t[static 24]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "25"(* num elems *), 8(* elem bytesize *));
    ("rc", "24"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("a", "25"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("sha3_keccak_f1600_alt2",
  ([(*args*)
     ("a", "uint64_t[static 25]", (*is const?*)"false");
     ("rc", "uint64_t[static 24]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("a", "25"(* num elems *), 8(* elem bytesize *));
    ("rc", "24"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("a", "25"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("sm2_montjadd",
  ([(*args*)
     ("p3", "uint64_t[static 12]", (*is const?*)"false");
     ("p1", "uint64_t[static 12]", (*is const?*)"true");
     ("p2", "uint64_t[static 12]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "12"(* num elems *), 8(* elem bytesize *));
    ("p2", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("sm2_montjadd_alt",
  ([(*args*)
     ("p3", "uint64_t[static 12]", (*is const?*)"false");
     ("p1", "uint64_t[static 12]", (*is const?*)"true");
     ("p2", "uint64_t[static 12]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "12"(* num elems *), 8(* elem bytesize *));
    ("p2", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("sm2_montjdouble",
  ([(*args*)
     ("p3", "uint64_t[static 12]", (*is const?*)"false");
     ("p1", "uint64_t[static 12]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("sm2_montjdouble_alt",
  ([(*args*)
     ("p3", "uint64_t[static 12]", (*is const?*)"false");
     ("p1", "uint64_t[static 12]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("sm2_montjmixadd",
  ([(*args*)
     ("p3", "uint64_t[static 12]", (*is const?*)"false");
     ("p1", "uint64_t[static 12]", (*is const?*)"true");
     ("p2", "uint64_t[static 8]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "12"(* num elems *), 8(* elem bytesize *));
    ("p2", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("sm2_montjmixadd_alt",
  ([(*args*)
     ("p3", "uint64_t[static 12]", (*is const?*)"false");
     ("p1", "uint64_t[static 12]", (*is const?*)"true");
     ("p2", "uint64_t[static 8]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("p1", "12"(* num elems *), 8(* elem bytesize *));
    ("p2", "8"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("p3", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("sm2_montjscalarmul",
  ([(*args*)
     ("res", "uint64_t[static 12]", (*is const?*)"false");
     ("scalar", "uint64_t[static 4]", (*is const?*)"true");
     ("point", "uint64_t[static 12]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "4"(* num elems *), 8(* elem bytesize *));
    ("point", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("sm2_montjscalarmul_alt",
  ([(*args*)
     ("res", "uint64_t[static 12]", (*is const?*)"false");
     ("scalar", "uint64_t[static 4]", (*is const?*)"true");
     ("point", "uint64_t[static 12]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("scalar", "4"(* num elems *), 8(* elem bytesize *));
    ("point", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("res", "12"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("word_bytereverse",
  ([(*args*)
     ("a", "uint64_t", (*is const?*)"false");
   ],
   "uint64_t",
   [(* input buffers *)
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("word_clz",
  ([(*args*)
     ("a", "uint64_t", (*is const?*)"false");
   ],
   "uint64_t",
   [(* input buffers *)
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("word_ctz",
  ([(*args*)
     ("a", "uint64_t", (*is const?*)"false");
   ],
   "uint64_t",
   [(* input buffers *)
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("word_divstep59",
  ([(*args*)
     ("m", "int64_t[2][2]", (*is const?*)"false");
     ("d", "int64_t", (*is const?*)"false");
     ("f", "uint64_t", (*is const?*)"false");
     ("g", "uint64_t", (*is const?*)"false");
   ],
   "int64_t",
   [(* input buffers *)
   ],
   [(* output buffers *)
    ("m", "2][2"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);

("word_max",
  ([(*args*)
     ("a", "uint64_t", (*is const?*)"false");
     ("b", "uint64_t", (*is const?*)"false");
   ],
   "uint64_t",
   [(* input buffers *)
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("word_min",
  ([(*args*)
     ("a", "uint64_t", (*is const?*)"false");
     ("b", "uint64_t", (*is const?*)"false");
   ],
   "uint64_t",
   [(* input buffers *)
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("word_negmodinv",
  ([(*args*)
     ("a", "uint64_t", (*is const?*)"false");
   ],
   "uint64_t",
   [(* input buffers *)
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("word_popcount",
  ([(*args*)
     ("a", "uint64_t", (*is const?*)"false");
   ],
   "uint64_t",
   [(* input buffers *)
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

("word_recip",
  ([(*args*)
     ("a", "uint64_t", (*is const?*)"false");
   ],
   "uint64_t",
   [(* input buffers *)
   ],
   [(* output buffers *)
   ],
   [(* temporary buffers *)
   ])
);

];;