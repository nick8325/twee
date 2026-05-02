cnf(a, conjecture, a1 = a2 & a2 = a3 & a3 = a4 & a4 = a5 & a5 = a6 &
a6 = a7 & a7 = a8 & a8 = a9 & a9 = a10 & a10 = a11 & a11 = a12 & a12 =
a13 & a13 = a14 & a14 = a15 & a15 = a16 & a16 = a17 & a17 = a18 & a18
= a19 & a19 = a20 & a20 = a21 & a20 = a22 & a21 = a23 & a23 = a24 &
a24 = a25 & a25 = a26 & a26 = a27 & a27 = a28 & a28 = a29 & a29 = a30
& a30 = a31 & a31 = a32 & a32 = a33 & a33 = a34 & a34 = a35 & a35 =
a36 & a36 = a37 & a37 = a38 & a38 = a39 & a39 = a40 & a40 = a41 & a41
= a42 & a42 = a43 & a43 = a44 & a44 = a45 & a45 = a46 & a46 = a47 &
a47 = a48 & a48 = a49 & a49 = a50 & a50 = a51 & a51 = a52 & a52 = a53
& a53 = a54 & a54 = a55 & a55 = a56 & a56 = a57 & a57 = a58 & a58 =
a59 & a59 = a60 & a60 = a61 & a61 = a62 & a62 = a63 & a63 = a64 & a64
= a65 & a65 = a66 & a66 = a67 & a67 = a68 & a68 = a69 & a69 = a70 &
a70 = a71 & a71 = a72 & a72 = a73 & a73 = a74 & a74 = a75 & a75 = a76
& a76 = a77 & a77 = a78 & a78 = a79 & a79 = a80 & a80 = a81 & a81 =
a82 & a82 = a83 & a83 = a84 & a84 = a85 & a85 = a86 & a86 = a87 & a87
= a88 & a88 = a89 & a89 = a90 & a90 = a91 & a91 = a92 & a92 = a93 &
a93 = a94 & a94 = a95 & a95 = a96 & a96 = a97 & a97 = a98 & a98 = a99
& a99 = a100 & a100 = a101 & a101 = a102 & a102 = a103 & a103 = a104 &
a104 = a105 & a105 = a106 & a106 = a107 & a107 = a108 & a108 = a109 &
a109 = a110 & a110 = a111 & a111 = a112 & a112 = a113 & a113 = a114 &
a114 = a115 & a115 = a116 & a116 = a117 & a117 = a118 & a118 = a119 &
a119 = a120 & a120 = a121 & a121 = a122 & a122 = a123 & a123 = a124 &
a124 = a125 & a125 = a126 & a126 = a127 & a127 = a128 & a128 = a129 &
a129 = a130 & a130 = a131 & a131 = a132 & a132 = a133 & a133 = a134 &
a134 = a135 & a135 = a136 & a136 = a137 & a137 = a138 & a138 = a139 &
a139 = a140 & a140 = a141).
cnf(a, axiom, '*'(X, X) = X).
cnf(a, axiom, '*'('*'(X,Y),Y) = X).
cnf(a, axiom, '*'('*'(X,Y),Z) = '*'('*'(X, Z), '*'(Y, Z))).
cnf(a, axiom, a2 = '*'(a1, a42)).
cnf(a, axiom, a3 = '*'(a2, a41)).
cnf(a, axiom, a4 = '*'(a3, a14)).
cnf(a, axiom, a5 = '*'(a4, a39)).
cnf(a, axiom, a6 = '*'(a5, a136)).
cnf(a, axiom, a7 = '*'(a6, a52)).
cnf(a, axiom, a8 = '*'(a7, a17)).
cnf(a, axiom, a9 = '*'(a8, a56)).
cnf(a, axiom, a10 = '*'(a9, a134)).
cnf(a, axiom, a11 = '*'(a10, a37)).
cnf(a, axiom, a12 = '*'(a11, a21)).
cnf(a, axiom, a13 = '*'(a12, a23)).
cnf(a, axiom, a14 = '*'(a13, a32)).
cnf(a, axiom, a15 = '*'(a14, a53)).
cnf(a, axiom, a16 = '*'(a15, a136)).
cnf(a, axiom, a17 = '*'(a16, a29)).
cnf(a, axiom, a18 = '*'(a17, a133)).
cnf(a, axiom, a19 = '*'(a18, a58)).
cnf(a, axiom, a20 = '*'(a19, a26)).
cnf(a, axiom, a21 = '*'(a20, a35)).
cnf(a, axiom, a22 = '*'(a21, a141)).
cnf(a, axiom, a23 = '*'(a22, a45)).
cnf(a, axiom, a24 = '*'(a23, a35)).
cnf(a, axiom, a25 = '*'(a24, a49)).
cnf(a, axiom, a26 = '*'(a25, a138)).
cnf(a, axiom, a27 = '*'(a26, a8)).
cnf(a, axiom, a28 = '*'(a27, a37)).
cnf(a, axiom, a29 = '*'(a28, a17)).
cnf(a, axiom, a30 = '*'(a29, a14)).
cnf(a, axiom, a31 = '*'(a30, a5)).
cnf(a, axiom, a32 = '*'(a31, a39)).
cnf(a, axiom, a33 = '*'(a32, a13)).
cnf(a, axiom, a34 = '*'(a33, a131)).
cnf(a, axiom, a35 = '*'(a34, a60)).
cnf(a, axiom, a36 = '*'(a35, a139)).
cnf(a, axiom, a37 = '*'(a36, a47)).
cnf(a, axiom, a38 = '*'(a37, a17)).
cnf(a, axiom, a39 = '*'(a38, a7)).
cnf(a, axiom, a40 = '*'(a39, a4)).
cnf(a, axiom, a41 = '*'(a40, a14)).
cnf(a, axiom, a42 = '*'(a41, a2)).
cnf(a, axiom, a43 = '*'(a42, a62)).
cnf(a, axiom, a44 = '*'(a43, a128)).
cnf(a, axiom, a45 = '*'(a44, a23)).
cnf(a, axiom, a46 = '*'(a45, a141)).
cnf(a, axiom, a47 = '*'(a46, a11)).
cnf(a, axiom, a48 = '*'(a47, a20)).
cnf(a, axiom, a49 = '*'(a48, a138)).
cnf(a, axiom, a50 = '*'(a49, a131)).
cnf(a, axiom, a51 = '*'(a50, a59)).
cnf(a, axiom, a52 = '*'(a51, a39)).
cnf(a, axiom, a53 = '*'(a52, a136)).
cnf(a, axiom, a54 = '*'(a53, a29)).
cnf(a, axiom, a55 = '*'(a54, a135)).
cnf(a, axiom, a56 = '*'(a55, a37)).
cnf(a, axiom, a57 = '*'(a56, a134)).
cnf(a, axiom, a58 = '*'(a57, a26)).
cnf(a, axiom, a59 = '*'(a58, a138)).
cnf(a, axiom, a60 = '*'(a59, a131)).
cnf(a, axiom, a61 = '*'(a60, a13)).
cnf(a, axiom, a62 = '*'(a61, a1)).
cnf(a, axiom, a63 = '*'(a62, a96)).
cnf(a, axiom, a64 = '*'(a63, a127)).
cnf(a, axiom, a65 = '*'(a64, a41)).
cnf(a, axiom, a66 = '*'(a65, a2)).
cnf(a, axiom, a67 = '*'(a66, a92)).
cnf(a, axiom, a68 = '*'(a67, a98)).
cnf(a, axiom, a69 = '*'(a68, a32)).
cnf(a, axiom, a70 = '*'(a69, a13)).
cnf(a, axiom, a71 = '*'(a70, a118)).
cnf(a, axiom, a72 = '*'(a71, a109)).
cnf(a, axiom, a73 = '*'(a72, a82)).
cnf(a, axiom, a74 = '*'(a73, a32)).
cnf(a, axiom, a75 = '*'(a74, a14)).
cnf(a, axiom, a76 = '*'(a75, a68)).
cnf(a, axiom, a77 = '*'(a76, a114)).
cnf(a, axiom, a78 = '*'(a77, a13)).
cnf(a, axiom, a79 = '*'(a78, a33)).
cnf(a, axiom, a80 = '*'(a79, a119)).
cnf(a, axiom, a81 = '*'(a80, a70)).
cnf(a, axiom, a82 = '*'(a81, a109)).
cnf(a, axiom, a83 = '*'(a82, a118)).
cnf(a, axiom, a84 = '*'(a83, a39)).
cnf(a, axiom, a85 = '*'(a84, a5)).
cnf(a, axiom, a86 = '*'(a85, a30)).
cnf(a, axiom, a87 = '*'(a86, a104)).
cnf(a, axiom, a88 = '*'(a87, a4)).
cnf(a, axiom, a89 = '*'(a88, a14)).
cnf(a, axiom, a90 = '*'(a89, a41)).
cnf(a, axiom, a91 = '*'(a90, a100)).
cnf(a, axiom, a92 = '*'(a91, a124)).
cnf(a, axiom, a93 = '*'(a92, a2)).
cnf(a, axiom, a94 = '*'(a93, a41)).
cnf(a, axiom, a95 = '*'(a94, a127)).
cnf(a, axiom, a96 = '*'(a95, a64)).
cnf(a, axiom, a97 = '*'(a96, a42)).
cnf(a, axiom, a98 = '*'(a97, a1)).
cnf(a, axiom, a99 = '*'(a98, a92)).
cnf(a, axiom, a100 = '*'(a99, a124)).
cnf(a, axiom, a101 = '*'(a100, a14)).
cnf(a, axiom, a102 = '*'(a101, a40)).
cnf(a, axiom, a103 = '*'(a102, a4)).
cnf(a, axiom, a104 = '*'(a103, a87)).
cnf(a, axiom, a105 = '*'(a104, a30)).
cnf(a, axiom, a106 = '*'(a105, a5)).
cnf(a, axiom, a107 = '*'(a106, a84)).
cnf(a, axiom, a108 = '*'(a107, a39)).
cnf(a, axiom, a109 = '*'(a108, a118)).
cnf(a, axiom, a110 = '*'(a109, a70)).
cnf(a, axiom, a111 = '*'(a110, a119)).
cnf(a, axiom, a112 = '*'(a111, a79)).
cnf(a, axiom, a113 = '*'(a112, a33)).
cnf(a, axiom, a114 = '*'(a113, a13)).
cnf(a, axiom, a115 = '*'(a114, a68)).
cnf(a, axiom, a116 = '*'(a115, a14)).
cnf(a, axiom, a117 = '*'(a116, a74)).
cnf(a, axiom, a118 = '*'(a117, a32)).
cnf(a, axiom, a119 = '*'(a118, a70)).
cnf(a, axiom, a120 = '*'(a119, a13)).
cnf(a, axiom, a121 = '*'(a120, a32)).
cnf(a, axiom, a122 = '*'(a121, a68)).
cnf(a, axiom, a123 = '*'(a122, a115)).
cnf(a, axiom, a124 = '*'(a123, a75)).
cnf(a, axiom, a125 = '*'(a124, a2)).
cnf(a, axiom, a126 = '*'(a125, a65)).
cnf(a, axiom, a127 = '*'(a126, a41)).
cnf(a, axiom, a128 = '*'(a127, a96)).
cnf(a, axiom, a129 = '*'(a128, a62)).
cnf(a, axiom, a130 = '*'(a129, a1)).
cnf(a, axiom, a131 = '*'(a130, a13)).
cnf(a, axiom, a132 = '*'(a131, a138)).
cnf(a, axiom, a133 = '*'(a132, a58)).
cnf(a, axiom, a134 = '*'(a133, a26)).
cnf(a, axiom, a135 = '*'(a134, a37)).
cnf(a, axiom, a136 = '*'(a135, a29)).
cnf(a, axiom, a137 = '*'(a136, a39)).
cnf(a, axiom, a138 = '*'(a137, a51)).
cnf(a, axiom, a139 = '*'(a138, a20)).
cnf(a, axiom, a140 = '*'(a139, a47)).
cnf(a, axiom, a141 = '*'(a140, a11)).
cnf(a, axiom, a1 = '*'(a141, a23)).
