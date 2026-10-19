"""C009 full-property Scott table with A1 split into A1a (no positive complementary pair) and
A1b (phi or its complement positive) (r1). Semantics as K3 (constant domain) and K14 (varying,
actualist, possibly empty domains): properties are all D -> W -> Prop, axioms global, Scott or
Goedel-1970 essence, G(x) := every positive property holds of x. Space: 64 subsets of
A1a,A1b,A2,A3,A4,A5 x essence (Goedel only with A5) x 9 classes = 864 cells x 4 outcomes.
Certificates: K3 countermodels (sha256-pinned; they satisfy both A1 halves, re-evaluated here with
E = all, so they are constant- and varying-domain models), one extra all-positive model (universal
2-world frame) for cells with A1b but without A1a, and Lean 4 core theorems whose hypotheses use
A1a only, with E a free parameter (entails_top: E = all is the constant-domain embedding)."""
DATA = r'''{"models":[[1,1,[],[[]]],[1,1,[],[[0]]],[1,1,[[0,0]],[[0]]],[2,1,[[0,1]],[[],[]]],[1,1,[[0,0]],[[]]],[2,1,[[0,0],[1,0]],[[],[]]],[2,1,[[0,0],[0,1],[1,1]],[[],[]]],[2,1,[[0,0],[0,1],[1,0],[1,1]],[[],[]]],[2,1,[[0,1],[1,0]],[[],[]]],[1,1,[],[[1]]],[2,1,[[0,1]],[[2,3],[2,3]]],[1,1,[[0,0]],[[1]]],[2,1,[[0,0],[1,0]],[[2,3],[2,3]]],[2,1,[[0,0],[0,1],[1,1]],[[2,3],[2,3]]],[2,1,[[0,0],[0,1],[1,0],[1,1]],[[2,3],[2,3]]],[2,1,[[0,1],[1,0]],[[2,3],[2,3]]],[1,1,[],[[0,1]]],[1,1,[[0,0]],[[0,1]]],[2,1,[[0,1]],[[3],[3]]],[2,1,[[0,0],[1,0]],[[3],[3]]],[2,1,[[0,0],[0,1],[1,1]],[[3],[3]]],[2,1,[[0,0],[0,1],[1,0],[1,1]],[[3],[3]]],[2,1,[[0,1],[1,0]],[[3],[3]]],[2,1,[[0,1]],[[2],[2]]],[2,1,[[0,0],[1,0]],[[1],[1]]],[2,1,[[0,0],[0,1],[1,1]],[[2],[2]]],[2,1,[[0,0],[0,1],[1,0],[1,1]],[[0],[0]]],[2,1,[[0,1],[1,0]],[[0],[0]]],[2,1,[[0,0],[1,0]],[[0],[0]]],[2,1,[[0,0],[0,1],[1,1]],[[0],[0]]],[2,1,[[0,0],[1,0]],[[1,3],[1,3]]],[2,1,[[0,1],[1,0]],[[2,3],[1,3]]],[2,1,[],[[2,3],[2,3]]],[2,1,[[0,0]],[[2,3],[2,3]]],[2,1,[[0,0],[1,0]],[[0,1],[1,3]]],[2,1,[[0,0],[1,1]],[[2,3],[2,3]]],[2,1,[[0,0],[0,1],[1,0],[1,1]],[[0,2],[0,2]]],[2,1,[[0,1],[1,0]],[[0,2],[0,2]]],[2,1,[[0,0],[1,0]],[[0,2],[0,2]]],[2,1,[[0,0],[0,1],[1,1]],[[0,2],[0,2]]],[2,1,[[0,1]],[[0,1,2,3],[0,1,2,3]]],[2,1,[[0,0],[0,1],[1,1]],[[3],[2,3]]],[2,1,[[0,1],[1,0]],[[0,1,2,3],[0,1,2,3]]],[2,1,[[0,1]],[[2,3],[0,1,2,3]]],[2,1,[[0,0],[0,1],[1,0],[1,1]],[[0,1,2,3],[0,1,2,3]]],[2,1,[[0,0],[1,0]],[[0,1,2,3],[0,1,2,3]]],[2,1,[[0,0],[0,1],[1,1]],[[0,1,2,3],[0,1,2,3]]],[2,1,[[0,0],[0,1],[1,0]],[[1,3],[1,3]]],[1,3,[[0,0]],[[3,5,6,7]]],[2,1,[[0,0],[1,0]],[[0,1],[0,1]]]],"cells":{"-|S|K":{"cons":[0,null,null],"concl":[1,0,null],"box":[2,0,0],"collapse":[3,null,null]},"-|S|D":{"cons":[4,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[5,null,null]},"-|S|T":{"cons":[4,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[6,null,null]},"-|S|B":{"cons":[4,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[7,null,null]},"-|S|K4":{"cons":[0,null,null],"concl":[1,0,null],"box":[2,0,0],"collapse":[3,null,null]},"-|S|KB":{"cons":[0,null,null],"concl":[1,0,null],"box":[2,0,0],"collapse":[8,null,null]},"-|S|KD45":{"cons":[4,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[5,null,null]},"-|S|S4":{"cons":[4,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[6,null,null]},"-|S|S5":{"cons":[4,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[7,null,null]},"A1|S|K":{"cons":[9,null,null],"concl":[1,0,null],"box":[2,0,0],"collapse":[10,null,null]},"A1|S|D":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[12,null,null]},"A1|S|T":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[13,null,null]},"A1|S|B":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[14,null,null]},"A1|S|K4":{"cons":[9,null,null],"concl":[1,0,null],"box":[2,0,0],"collapse":[10,null,null]},"A1|S|KB":{"cons":[9,null,null],"concl":[1,0,null],"box":[2,0,0],"collapse":[15,null,null]},"A1|S|KD45":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[12,null,null]},"A1|S|S4":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[13,null,null]},"A1|S|S5":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[14,null,null]},"A2|S|K":{"cons":[0,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[3,null,null]},"A2|S|D":{"cons":[4,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[5,null,null]},"A2|S|T":{"cons":[4,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[6,null,null]},"A2|S|B":{"cons":[4,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[7,null,null]},"A2|S|K4":{"cons":[0,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[3,null,null]},"A2|S|KB":{"cons":[0,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[8,null,null]},"A2|S|KD45":{"cons":[4,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[5,null,null]},"A2|S|S4":{"cons":[4,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[6,null,null]},"A2|S|S5":{"cons":[4,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[7,null,null]},"A3|S|K":{"cons":[9,null,null],"concl":[1,0,null],"box":[2,0,0],"collapse":[18,null,null]},"A3|S|D":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[19,null,null]},"A3|S|T":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[20,null,null]},"A3|S|B":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[21,null,null]},"A3|S|K4":{"cons":[9,null,null],"concl":[1,0,null],"box":[2,0,0],"collapse":[18,null,null]},"A3|S|KB":{"cons":[9,null,null],"concl":[1,0,null],"box":[2,0,0],"collapse":[22,null,null]},"A3|S|KD45":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[19,null,null]},"A3|S|S4":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[20,null,null]},"A3|S|S5":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[21,null,null]},"A4|S|K":{"cons":[0,null,null],"concl":[1,0,null],"box":[2,0,0],"collapse":[3,null,null]},"A4|S|D":{"cons":[4,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[5,null,null]},"A4|S|T":{"cons":[4,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[6,null,null]},"A4|S|B":{"cons":[4,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[7,null,null]},"A4|S|K4":{"cons":[0,null,null],"concl":[1,0,null],"box":[2,0,0],"collapse":[3,null,null]},"A4|S|KB":{"cons":[0,null,null],"concl":[1,0,null],"box":[2,0,0],"collapse":[8,null,null]},"A4|S|KD45":{"cons":[4,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[5,null,null]},"A4|S|S4":{"cons":[4,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[6,null,null]},"A4|S|S5":{"cons":[4,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[7,null,null]},"A5|S|K":{"cons":[9,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[23,null,null]},"A5|S|D":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[24,null,null]},"A5|S|T":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[25,null,null]},"A5|S|B":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[26,null,null]},"A5|S|K4":{"cons":[9,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[23,null,null]},"A5|S|KB":{"cons":[9,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[27,null,null]},"A5|S|KD45":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[24,null,null]},"A5|S|S4":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[25,null,null]},"A5|S|S5":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[26,null,null]},"A5|G|K":{"cons":[9,null,null],"concl":[16,0,null],"box":[2,0,0],"collapse":[23,null,null]},"A5|G|D":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[28,null,null]},"A5|G|T":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[29,null,null]},"A5|G|B":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[26,null,null]},"A5|G|K4":{"cons":[9,null,null],"concl":[16,0,null],"box":[2,0,0],"collapse":[23,null,null]},"A5|G|KB":{"cons":[9,null,null],"concl":[16,0,null],"box":[2,0,0],"collapse":[27,null,null]},"A5|G|KD45":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[28,null,null]},"A5|G|S4":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[29,null,null]},"A5|G|S5":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[26,null,null]},"A1+A2|S|K":{"cons":[11,null,null],"concl":[30,1,null],"box":[31,0,1],"collapse":[30,null,null]},"A1+A2|S|D":{"cons":[11,null,null],"concl":[30,1,null],"box":[31,0,1],"collapse":[30,null,null]},"A1+A2|S|T":{"cons":[11,null,null],"concl":[13,0,null],"box":[13,0,0],"collapse":[13,null,null]},"A1+A2|S|B":{"cons":[11,null,null],"concl":[14,0,null],"box":[14,0,0],"collapse":[14,null,null]},"A1+A2|S|K4":{"cons":[11,null,null],"concl":[30,1,null],"box":[13,0,0],"collapse":[30,null,null]},"A1+A2|S|KB":{"cons":[11,null,null],"concl":[31,0,null],"box":[31,0,1],"collapse":[31,null,null]},"A1+A2|S|KD45":{"cons":[11,null,null],"concl":[30,1,null],"box":[14,0,0],"collapse":[30,null,null]},"A1+A2|S|S4":{"cons":[11,null,null],"concl":[13,0,null],"box":[13,0,0],"collapse":[13,null,null]},"A1+A2|S|S5":{"cons":[11,null,null],"concl":[14,0,null],"box":[14,0,0],"collapse":[14,null,null]},"A1+A3|S|K":{"cons":[9,null,null],"concl":[1,0,null],"box":[2,0,0],"collapse":[10,null,null]},"A1+A3|S|D":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[12,null,null]},"A1+A3|S|T":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[13,null,null]},"A1+A3|S|B":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[14,null,null]},"A1+A3|S|K4":{"cons":[9,null,null],"concl":[1,0,null],"box":[2,0,0],"collapse":[10,null,null]},"A1+A3|S|KB":{"cons":[9,null,null],"concl":[1,0,null],"box":[2,0,0],"collapse":[15,null,null]},"A1+A3|S|KD45":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[12,null,null]},"A1+A3|S|S4":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[13,null,null]},"A1+A3|S|S5":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[14,null,null]},"A1+A4|S|K":{"cons":[9,null,null],"concl":[1,0,null],"box":[2,0,0],"collapse":[10,null,null]},"A1+A4|S|D":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[12,null,null]},"A1+A4|S|T":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[13,null,null]},"A1+A4|S|B":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[14,null,null]},"A1+A4|S|K4":{"cons":[9,null,null],"concl":[1,0,null],"box":[2,0,0],"collapse":[10,null,null]},"A1+A4|S|KB":{"cons":[9,null,null],"concl":[1,0,null],"box":[2,0,0],"collapse":[15,null,null]},"A1+A4|S|KD45":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[12,null,null]},"A1+A4|S|S4":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[13,null,null]},"A1+A4|S|S5":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[14,null,null]},"A1+A5|S|K":{"cons":[9,null,null],"concl":[32,0,null],"box":[33,0,0],"collapse":[10,null,null]},"A1+A5|S|D":{"cons":[11,null,null],"concl":[34,0,null],"box":[34,0,0],"collapse":[30,null,null]},"A1+A5|S|T":{"cons":[11,null,null],"concl":[35,0,null],"box":[35,0,0],"collapse":[13,null,null]},"A1+A5|S|B":{"cons":[11,null,null],"concl":[35,0,null],"box":[35,0,0],"collapse":[36,null,null]},"A1+A5|S|K4":{"cons":[9,null,null],"concl":[32,0,null],"box":[33,0,0],"collapse":[10,null,null]},"A1+A5|S|KB":{"cons":[9,null,null],"concl":[32,0,null],"box":[33,0,0],"collapse":[37,null,null]},"A1+A5|S|KD45":{"cons":[11,null,null],"concl":[34,0,null],"box":[34,0,0],"collapse":[30,null,null]},"A1+A5|S|S4":{"cons":[11,null,null],"concl":[35,0,null],"box":[35,0,0],"collapse":[13,null,null]},"A1+A5|S|S5":{"cons":[11,null,null],"concl":[35,0,null],"box":[35,0,0],"collapse":[36,null,null]},"A1+A5|G|K":{"cons":[9,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[10,null,null]},"A1+A5|G|D":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[38,null,null]},"A1+A5|G|T":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[39,null,null]},"A1+A5|G|B":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[36,null,null]},"A1+A5|G|K4":{"cons":[9,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[10,null,null]},"A1+A5|G|KB":{"cons":[9,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[37,null,null]},"A1+A5|G|KD45":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[38,null,null]},"A1+A5|G|S4":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[39,null,null]},"A1+A5|G|S5":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[36,null,null]},"A2+A3|S|K":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[40,null,null]},"A2+A3|S|D":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[30,null,null]},"A2+A3|S|T":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[41,null,null]},"A2+A3|S|B":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[21,null,null]},"A2+A3|S|K4":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[40,null,null]},"A2+A3|S|KB":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[42,null,null]},"A2+A3|S|KD45":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[30,null,null]},"A2+A3|S|S4":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[41,null,null]},"A2+A3|S|S5":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[21,null,null]},"A2+A4|S|K":{"cons":[0,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[3,null,null]},"A2+A4|S|D":{"cons":[4,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[5,null,null]},"A2+A4|S|T":{"cons":[4,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[6,null,null]},"A2+A4|S|B":{"cons":[4,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[7,null,null]},"A2+A4|S|K4":{"cons":[0,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[3,null,null]},"A2+A4|S|KB":{"cons":[0,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[8,null,null]},"A2+A4|S|KD45":{"cons":[4,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[5,null,null]},"A2+A4|S|S4":{"cons":[4,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[6,null,null]},"A2+A4|S|S5":{"cons":[4,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[7,null,null]},"A2+A5|S|K":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[43,null,null]},"A2+A5|S|D":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[30,null,null]},"A2+A5|S|T":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[13,null,null]},"A2+A5|S|B":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[44,null,null]},"A2+A5|S|K4":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[43,null,null]},"A2+A5|S|KB":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[42,null,null]},"A2+A5|S|KD45":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[30,null,null]},"A2+A5|S|S4":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[13,null,null]},"A2+A5|S|S5":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[44,null,null]},"A2+A5|G|K":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[43,null,null]},"A2+A5|G|D":{"cons":[17,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[45,null,null]},"A2+A5|G|T":{"cons":[17,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[46,null,null]},"A2+A5|G|B":{"cons":[17,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[44,null,null]},"A2+A5|G|K4":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[43,null,null]},"A2+A5|G|KB":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[42,null,null]},"A2+A5|G|KD45":{"cons":[17,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[45,null,null]},"A2+A5|G|S4":{"cons":[17,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[46,null,null]},"A2+A5|G|S5":{"cons":[17,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[44,null,null]},"A3+A4|S|K":{"cons":[9,null,null],"concl":[1,0,null],"box":[2,0,0],"collapse":[18,null,null]},"A3+A4|S|D":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[19,null,null]},"A3+A4|S|T":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[20,null,null]},"A3+A4|S|B":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[21,null,null]},"A3+A4|S|K4":{"cons":[9,null,null],"concl":[1,0,null],"box":[2,0,0],"collapse":[18,null,null]},"A3+A4|S|KB":{"cons":[9,null,null],"concl":[1,0,null],"box":[2,0,0],"collapse":[22,null,null]},"A3+A4|S|KD45":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[19,null,null]},"A3+A4|S|S4":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[20,null,null]},"A3+A4|S|S5":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[21,null,null]},"A3+A5|S|K":{"cons":[9,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[23,null,null]},"A3+A5|S|D":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[24,null,null]},"A3+A5|S|T":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[25,null,null]},"A3+A5|S|B":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[26,null,null]},"A3+A5|S|K4":{"cons":[9,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[23,null,null]},"A3+A5|S|KB":{"cons":[9,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[27,null,null]},"A3+A5|S|KD45":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[24,null,null]},"A3+A5|S|S4":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[25,null,null]},"A3+A5|S|S5":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[26,null,null]},"A3+A5|G|K":{"cons":[9,null,null],"concl":[16,0,null],"box":[2,0,0],"collapse":[23,null,null]},"A3+A5|G|D":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[28,null,null]},"A3+A5|G|T":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[29,null,null]},"A3+A5|G|B":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[26,null,null]},"A3+A5|G|K4":{"cons":[9,null,null],"concl":[16,0,null],"box":[2,0,0],"collapse":[23,null,null]},"A3+A5|G|KB":{"cons":[9,null,null],"concl":[16,0,null],"box":[2,0,0],"collapse":[27,null,null]},"A3+A5|G|KD45":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[28,null,null]},"A3+A5|G|S4":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[29,null,null]},"A3+A5|G|S5":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[26,null,null]},"A4+A5|S|K":{"cons":[9,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[23,null,null]},"A4+A5|S|D":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[24,null,null]},"A4+A5|S|T":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[25,null,null]},"A4+A5|S|B":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[26,null,null]},"A4+A5|S|K4":{"cons":[9,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[23,null,null]},"A4+A5|S|KB":{"cons":[9,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[27,null,null]},"A4+A5|S|KD45":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[24,null,null]},"A4+A5|S|S4":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[25,null,null]},"A4+A5|S|S5":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[26,null,null]},"A4+A5|G|K":{"cons":[9,null,null],"concl":[16,0,null],"box":[2,0,0],"collapse":[23,null,null]},"A4+A5|G|D":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[28,null,null]},"A4+A5|G|T":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[29,null,null]},"A4+A5|G|B":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[26,null,null]},"A4+A5|G|K4":{"cons":[9,null,null],"concl":[16,0,null],"box":[2,0,0],"collapse":[23,null,null]},"A4+A5|G|KB":{"cons":[9,null,null],"concl":[16,0,null],"box":[2,0,0],"collapse":[27,null,null]},"A4+A5|G|KD45":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[28,null,null]},"A4+A5|G|S4":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[29,null,null]},"A4+A5|G|S5":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[26,null,null]},"A1+A2+A3|S|K":{"cons":[11,null,null],"concl":[30,1,null],"box":[47,0,1],"collapse":[30,null,null]},"A1+A2+A3|S|D":{"cons":[11,null,null],"concl":[30,1,null],"box":[47,0,1],"collapse":[30,null,null]},"A1+A2+A3|S|T":{"cons":[11,null,null],"concl":[13,0,null],"box":[13,0,0],"collapse":[13,null,null]},"A1+A2+A3|S|B":{"cons":[11,null,null],"concl":[14,0,null],"box":[14,0,0],"collapse":[14,null,null]},"A1+A2+A3|S|K4":{"cons":[11,null,null],"concl":[30,1,null],"box":[13,0,0],"collapse":[30,null,null]},"A1+A2+A3|S|KB":{"cons":[11,null,null],"concl":[47,1,null],"box":[47,0,1],"collapse":[47,null,null]},"A1+A2+A3|S|KD45":{"cons":[11,null,null],"concl":[30,1,null],"box":[14,0,0],"collapse":[30,null,null]},"A1+A2+A3|S|S4":{"cons":[11,null,null],"concl":[13,0,null],"box":[13,0,0],"collapse":[13,null,null]},"A1+A2+A3|S|S5":{"cons":[11,null,null],"concl":[14,0,null],"box":[14,0,0],"collapse":[14,null,null]},"A1+A2+A4|S|K":{"cons":[11,null,null],"concl":[30,1,null],"box":[47,0,1],"collapse":[30,null,null]},"A1+A2+A4|S|D":{"cons":[11,null,null],"concl":[30,1,null],"box":[47,0,1],"collapse":[30,null,null]},"A1+A2+A4|S|T":{"cons":[11,null,null],"concl":[13,0,null],"box":[13,0,0],"collapse":[13,null,null]},"A1+A2+A4|S|B":{"cons":[11,null,null],"concl":[14,0,null],"box":[14,0,0],"collapse":[14,null,null]},"A1+A2+A4|S|K4":{"cons":[11,null,null],"concl":[30,1,null],"box":[13,0,0],"collapse":[30,null,null]},"A1+A2+A4|S|KB":{"cons":[11,null,null],"concl":[47,1,null],"box":[47,0,1],"collapse":[47,null,null]},"A1+A2+A4|S|KD45":{"cons":[11,null,null],"concl":[30,1,null],"box":[14,0,0],"collapse":[30,null,null]},"A1+A2+A4|S|S4":{"cons":[11,null,null],"concl":[13,0,null],"box":[13,0,0],"collapse":[13,null,null]},"A1+A2+A4|S|S5":{"cons":[11,null,null],"concl":[14,0,null],"box":[14,0,0],"collapse":[14,null,null]},"A1+A2+A5|S|K":{"cons":[11,null,null],"concl":[30,1,null],"box":[13,0,0],"collapse":[30,null,null]},"A1+A2+A5|S|D":{"cons":[11,null,null],"concl":[30,1,null],"box":[13,0,0],"collapse":[30,null,null]},"A1+A2+A5|S|T":{"cons":[11,null,null],"concl":[13,0,null],"box":[13,0,0],"collapse":[13,null,null]},"A1+A2+A5|S|B":{"cons":[11,null,null],"concl":[48,0,null],"box":[48,0,0],"collapse":null},"A1+A2+A5|S|K4":{"cons":[11,null,null],"concl":[30,1,null],"box":[13,0,0],"collapse":[30,null,null]},"A1+A2+A5|S|KB":{"cons":[11,null,null],"concl":[48,0,null],"box":[48,0,0],"collapse":null},"A1+A2+A5|S|KD45":{"cons":[11,null,null],"concl":[30,1,null],"box":[48,0,0],"collapse":[30,null,null]},"A1+A2+A5|S|S4":{"cons":[11,null,null],"concl":[13,0,null],"box":[13,0,0],"collapse":[13,null,null]},"A1+A2+A5|S|S5":{"cons":[11,null,null],"concl":[48,0,null],"box":[48,0,0],"collapse":null},"A1+A2+A5|G|K":"X","A1+A2+A5|G|D":"X","A1+A2+A5|G|T":"X","A1+A2+A5|G|B":"X","A1+A2+A5|G|K4":"X","A1+A2+A5|G|KB":"X","A1+A2+A5|G|KD45":"X","A1+A2+A5|G|S4":"X","A1+A2+A5|G|S5":"X","A1+A3+A4|S|K":{"cons":[9,null,null],"concl":[1,0,null],"box":[2,0,0],"collapse":[10,null,null]},"A1+A3+A4|S|D":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[12,null,null]},"A1+A3+A4|S|T":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[13,null,null]},"A1+A3+A4|S|B":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[14,null,null]},"A1+A3+A4|S|K4":{"cons":[9,null,null],"concl":[1,0,null],"box":[2,0,0],"collapse":[10,null,null]},"A1+A3+A4|S|KB":{"cons":[9,null,null],"concl":[1,0,null],"box":[2,0,0],"collapse":[15,null,null]},"A1+A3+A4|S|KD45":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[12,null,null]},"A1+A3+A4|S|S4":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[13,null,null]},"A1+A3+A4|S|S5":{"cons":[11,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[14,null,null]},"A1+A3+A5|S|K":{"cons":[9,null,null],"concl":[32,0,null],"box":[33,0,0],"collapse":[10,null,null]},"A1+A3+A5|S|D":{"cons":[11,null,null],"concl":[49,0,null],"box":[49,0,0],"collapse":[30,null,null]},"A1+A3+A5|S|T":{"cons":[11,null,null],"concl":[35,0,null],"box":[35,0,0],"collapse":[13,null,null]},"A1+A3+A5|S|B":{"cons":[11,null,null],"concl":[35,0,null],"box":[35,0,0],"collapse":[36,null,null]},"A1+A3+A5|S|K4":{"cons":[9,null,null],"concl":[32,0,null],"box":[33,0,0],"collapse":[10,null,null]},"A1+A3+A5|S|KB":{"cons":[9,null,null],"concl":[32,0,null],"box":[33,0,0],"collapse":[37,null,null]},"A1+A3+A5|S|KD45":{"cons":[11,null,null],"concl":[49,0,null],"box":[49,0,0],"collapse":[30,null,null]},"A1+A3+A5|S|S4":{"cons":[11,null,null],"concl":[35,0,null],"box":[35,0,0],"collapse":[13,null,null]},"A1+A3+A5|S|S5":{"cons":[11,null,null],"concl":[35,0,null],"box":[35,0,0],"collapse":[36,null,null]},"A1+A3+A5|G|K":{"cons":[9,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[10,null,null]},"A1+A3+A5|G|D":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[38,null,null]},"A1+A3+A5|G|T":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[39,null,null]},"A1+A3+A5|G|B":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[36,null,null]},"A1+A3+A5|G|K4":{"cons":[9,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[10,null,null]},"A1+A3+A5|G|KB":{"cons":[9,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[37,null,null]},"A1+A3+A5|G|KD45":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[38,null,null]},"A1+A3+A5|G|S4":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[39,null,null]},"A1+A3+A5|G|S5":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[36,null,null]},"A1+A4+A5|S|K":{"cons":[9,null,null],"concl":[32,0,null],"box":[33,0,0],"collapse":[10,null,null]},"A1+A4+A5|S|D":{"cons":[11,null,null],"concl":[49,0,null],"box":[49,0,0],"collapse":[30,null,null]},"A1+A4+A5|S|T":{"cons":[11,null,null],"concl":[35,0,null],"box":[35,0,0],"collapse":[13,null,null]},"A1+A4+A5|S|B":{"cons":[11,null,null],"concl":[35,0,null],"box":[35,0,0],"collapse":[36,null,null]},"A1+A4+A5|S|K4":{"cons":[9,null,null],"concl":[32,0,null],"box":[33,0,0],"collapse":[10,null,null]},"A1+A4+A5|S|KB":{"cons":[9,null,null],"concl":[32,0,null],"box":[33,0,0],"collapse":[37,null,null]},"A1+A4+A5|S|KD45":{"cons":[11,null,null],"concl":[49,0,null],"box":[49,0,0],"collapse":[30,null,null]},"A1+A4+A5|S|S4":{"cons":[11,null,null],"concl":[35,0,null],"box":[35,0,0],"collapse":[13,null,null]},"A1+A4+A5|S|S5":{"cons":[11,null,null],"concl":[35,0,null],"box":[35,0,0],"collapse":[36,null,null]},"A1+A4+A5|G|K":{"cons":[9,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[10,null,null]},"A1+A4+A5|G|D":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[38,null,null]},"A1+A4+A5|G|T":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[39,null,null]},"A1+A4+A5|G|B":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[36,null,null]},"A1+A4+A5|G|K4":{"cons":[9,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[10,null,null]},"A1+A4+A5|G|KB":{"cons":[9,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[37,null,null]},"A1+A4+A5|G|KD45":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[38,null,null]},"A1+A4+A5|G|S4":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[39,null,null]},"A1+A4+A5|G|S5":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[36,null,null]},"A2+A3+A4|S|K":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[40,null,null]},"A2+A3+A4|S|D":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[30,null,null]},"A2+A3+A4|S|T":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[41,null,null]},"A2+A3+A4|S|B":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[21,null,null]},"A2+A3+A4|S|K4":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[40,null,null]},"A2+A3+A4|S|KB":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[42,null,null]},"A2+A3+A4|S|KD45":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[30,null,null]},"A2+A3+A4|S|S4":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[41,null,null]},"A2+A3+A4|S|S5":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[21,null,null]},"A2+A3+A5|S|K":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[40,null,null]},"A2+A3+A5|S|D":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[30,null,null]},"A2+A3+A5|S|T":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[13,null,null]},"A2+A3+A5|S|B":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[44,null,null]},"A2+A3+A5|S|K4":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[40,null,null]},"A2+A3+A5|S|KB":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[42,null,null]},"A2+A3+A5|S|KD45":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[30,null,null]},"A2+A3+A5|S|S4":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[13,null,null]},"A2+A3+A5|S|S5":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[44,null,null]},"A2+A3+A5|G|K":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[40,null,null]},"A2+A3+A5|G|D":{"cons":[17,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[45,null,null]},"A2+A3+A5|G|T":{"cons":[17,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[46,null,null]},"A2+A3+A5|G|B":{"cons":[17,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[44,null,null]},"A2+A3+A5|G|K4":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[40,null,null]},"A2+A3+A5|G|KB":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[42,null,null]},"A2+A3+A5|G|KD45":{"cons":[17,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[45,null,null]},"A2+A3+A5|G|S4":{"cons":[17,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[46,null,null]},"A2+A3+A5|G|S5":{"cons":[17,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[44,null,null]},"A2+A4+A5|S|K":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[43,null,null]},"A2+A4+A5|S|D":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[30,null,null]},"A2+A4+A5|S|T":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[13,null,null]},"A2+A4+A5|S|B":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[44,null,null]},"A2+A4+A5|S|K4":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[43,null,null]},"A2+A4+A5|S|KB":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[42,null,null]},"A2+A4+A5|S|KD45":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[30,null,null]},"A2+A4+A5|S|S4":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[13,null,null]},"A2+A4+A5|S|S5":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[44,null,null]},"A2+A4+A5|G|K":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[43,null,null]},"A2+A4+A5|G|D":{"cons":[17,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[45,null,null]},"A2+A4+A5|G|T":{"cons":[17,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[46,null,null]},"A2+A4+A5|G|B":{"cons":[17,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[44,null,null]},"A2+A4+A5|G|K4":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[43,null,null]},"A2+A4+A5|G|KB":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[42,null,null]},"A2+A4+A5|G|KD45":{"cons":[17,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[45,null,null]},"A2+A4+A5|G|S4":{"cons":[17,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[46,null,null]},"A2+A4+A5|G|S5":{"cons":[17,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[44,null,null]},"A3+A4+A5|S|K":{"cons":[9,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[23,null,null]},"A3+A4+A5|S|D":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[24,null,null]},"A3+A4+A5|S|T":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[25,null,null]},"A3+A4+A5|S|B":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[26,null,null]},"A3+A4+A5|S|K4":{"cons":[9,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[23,null,null]},"A3+A4+A5|S|KB":{"cons":[9,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[27,null,null]},"A3+A4+A5|S|KD45":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[24,null,null]},"A3+A4+A5|S|S4":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[25,null,null]},"A3+A4+A5|S|S5":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[26,null,null]},"A3+A4+A5|G|K":{"cons":[9,null,null],"concl":[16,0,null],"box":[2,0,0],"collapse":[23,null,null]},"A3+A4+A5|G|D":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[28,null,null]},"A3+A4+A5|G|T":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[29,null,null]},"A3+A4+A5|G|B":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[26,null,null]},"A3+A4+A5|G|K4":{"cons":[9,null,null],"concl":[16,0,null],"box":[2,0,0],"collapse":[23,null,null]},"A3+A4+A5|G|KB":{"cons":[9,null,null],"concl":[16,0,null],"box":[2,0,0],"collapse":[27,null,null]},"A3+A4+A5|G|KD45":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[28,null,null]},"A3+A4+A5|G|S4":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[29,null,null]},"A3+A4+A5|G|S5":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[26,null,null]},"A1+A2+A3+A4|S|K":{"cons":[11,null,null],"concl":[30,1,null],"box":[47,0,1],"collapse":[30,null,null]},"A1+A2+A3+A4|S|D":{"cons":[11,null,null],"concl":[30,1,null],"box":[47,0,1],"collapse":[30,null,null]},"A1+A2+A3+A4|S|T":{"cons":[11,null,null],"concl":[13,0,null],"box":[13,0,0],"collapse":[13,null,null]},"A1+A2+A3+A4|S|B":{"cons":[11,null,null],"concl":[14,0,null],"box":[14,0,0],"collapse":[14,null,null]},"A1+A2+A3+A4|S|K4":{"cons":[11,null,null],"concl":[30,1,null],"box":[13,0,0],"collapse":[30,null,null]},"A1+A2+A3+A4|S|KB":{"cons":[11,null,null],"concl":[47,1,null],"box":[47,0,1],"collapse":[47,null,null]},"A1+A2+A3+A4|S|KD45":{"cons":[11,null,null],"concl":[30,1,null],"box":[14,0,0],"collapse":[30,null,null]},"A1+A2+A3+A4|S|S4":{"cons":[11,null,null],"concl":[13,0,null],"box":[13,0,0],"collapse":[13,null,null]},"A1+A2+A3+A4|S|S5":{"cons":[11,null,null],"concl":[14,0,null],"box":[14,0,0],"collapse":[14,null,null]},"A1+A2+A3+A5|S|K":{"cons":[11,null,null],"concl":[30,1,null],"box":[13,0,0],"collapse":[30,null,null]},"A1+A2+A3+A5|S|D":{"cons":[11,null,null],"concl":[30,1,null],"box":[13,0,0],"collapse":[30,null,null]},"A1+A2+A3+A5|S|T":{"cons":[11,null,null],"concl":[13,0,null],"box":[13,0,0],"collapse":[13,null,null]},"A1+A2+A3+A5|S|B":{"cons":[11,null,null],"concl":null,"box":null,"collapse":null},"A1+A2+A3+A5|S|K4":{"cons":[11,null,null],"concl":[30,1,null],"box":[13,0,0],"collapse":[30,null,null]},"A1+A2+A3+A5|S|KB":{"cons":[11,null,null],"concl":null,"box":null,"collapse":null},"A1+A2+A3+A5|S|KD45":{"cons":[11,null,null],"concl":[30,1,null],"box":null,"collapse":[30,null,null]},"A1+A2+A3+A5|S|S4":{"cons":[11,null,null],"concl":[13,0,null],"box":[13,0,0],"collapse":[13,null,null]},"A1+A2+A3+A5|S|S5":{"cons":[11,null,null],"concl":null,"box":null,"collapse":null},"A1+A2+A3+A5|G|K":"X","A1+A2+A3+A5|G|D":"X","A1+A2+A3+A5|G|T":"X","A1+A2+A3+A5|G|B":"X","A1+A2+A3+A5|G|K4":"X","A1+A2+A3+A5|G|KB":"X","A1+A2+A3+A5|G|KD45":"X","A1+A2+A3+A5|G|S4":"X","A1+A2+A3+A5|G|S5":"X","A1+A2+A4+A5|S|K":{"cons":[11,null,null],"concl":[30,1,null],"box":[13,0,0],"collapse":[30,null,null]},"A1+A2+A4+A5|S|D":{"cons":[11,null,null],"concl":[30,1,null],"box":[13,0,0],"collapse":[30,null,null]},"A1+A2+A4+A5|S|T":{"cons":[11,null,null],"concl":[13,0,null],"box":[13,0,0],"collapse":[13,null,null]},"A1+A2+A4+A5|S|B":{"cons":[11,null,null],"concl":[48,0,null],"box":[48,0,0],"collapse":null},"A1+A2+A4+A5|S|K4":{"cons":[11,null,null],"concl":[30,1,null],"box":[13,0,0],"collapse":[30,null,null]},"A1+A2+A4+A5|S|KB":{"cons":[11,null,null],"concl":[48,0,null],"box":[48,0,0],"collapse":null},"A1+A2+A4+A5|S|KD45":{"cons":[11,null,null],"concl":[30,1,null],"box":[48,0,0],"collapse":[30,null,null]},"A1+A2+A4+A5|S|S4":{"cons":[11,null,null],"concl":[13,0,null],"box":[13,0,0],"collapse":[13,null,null]},"A1+A2+A4+A5|S|S5":{"cons":[11,null,null],"concl":[48,0,null],"box":[48,0,0],"collapse":null},"A1+A2+A4+A5|G|K":"X","A1+A2+A4+A5|G|D":"X","A1+A2+A4+A5|G|T":"X","A1+A2+A4+A5|G|B":"X","A1+A2+A4+A5|G|K4":"X","A1+A2+A4+A5|G|KB":"X","A1+A2+A4+A5|G|KD45":"X","A1+A2+A4+A5|G|S4":"X","A1+A2+A4+A5|G|S5":"X","A1+A3+A4+A5|S|K":{"cons":[9,null,null],"concl":[32,0,null],"box":[33,0,0],"collapse":[10,null,null]},"A1+A3+A4+A5|S|D":{"cons":[11,null,null],"concl":[49,0,null],"box":[49,0,0],"collapse":[30,null,null]},"A1+A3+A4+A5|S|T":{"cons":[11,null,null],"concl":[35,0,null],"box":[35,0,0],"collapse":[13,null,null]},"A1+A3+A4+A5|S|B":{"cons":[11,null,null],"concl":[35,0,null],"box":[35,0,0],"collapse":[36,null,null]},"A1+A3+A4+A5|S|K4":{"cons":[9,null,null],"concl":[32,0,null],"box":[33,0,0],"collapse":[10,null,null]},"A1+A3+A4+A5|S|KB":{"cons":[9,null,null],"concl":[32,0,null],"box":[33,0,0],"collapse":[37,null,null]},"A1+A3+A4+A5|S|KD45":{"cons":[11,null,null],"concl":[49,0,null],"box":[49,0,0],"collapse":[30,null,null]},"A1+A3+A4+A5|S|S4":{"cons":[11,null,null],"concl":[35,0,null],"box":[35,0,0],"collapse":[13,null,null]},"A1+A3+A4+A5|S|S5":{"cons":[11,null,null],"concl":[35,0,null],"box":[35,0,0],"collapse":[36,null,null]},"A1+A3+A4+A5|G|K":{"cons":[9,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[10,null,null]},"A1+A3+A4+A5|G|D":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[38,null,null]},"A1+A3+A4+A5|G|T":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[39,null,null]},"A1+A3+A4+A5|G|B":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[36,null,null]},"A1+A3+A4+A5|G|K4":{"cons":[9,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[10,null,null]},"A1+A3+A4+A5|G|KB":{"cons":[9,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[37,null,null]},"A1+A3+A4+A5|G|KD45":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[38,null,null]},"A1+A3+A4+A5|G|S4":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[39,null,null]},"A1+A3+A4+A5|G|S5":{"cons":[2,null,null],"concl":[2,0,null],"box":[2,0,0],"collapse":[36,null,null]},"A2+A3+A4+A5|S|K":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[40,null,null]},"A2+A3+A4+A5|S|D":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[30,null,null]},"A2+A3+A4+A5|S|T":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[13,null,null]},"A2+A3+A4+A5|S|B":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[44,null,null]},"A2+A3+A4+A5|S|K4":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[40,null,null]},"A2+A3+A4+A5|S|KB":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[42,null,null]},"A2+A3+A4+A5|S|KD45":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[30,null,null]},"A2+A3+A4+A5|S|S4":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[13,null,null]},"A2+A3+A4+A5|S|S5":{"cons":[11,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[44,null,null]},"A2+A3+A4+A5|G|K":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[40,null,null]},"A2+A3+A4+A5|G|D":{"cons":[17,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[45,null,null]},"A2+A3+A4+A5|G|T":{"cons":[17,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[46,null,null]},"A2+A3+A4+A5|G|B":{"cons":[17,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[44,null,null]},"A2+A3+A4+A5|G|K4":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[40,null,null]},"A2+A3+A4+A5|G|KB":{"cons":[16,null,null],"concl":[16,0,null],"box":[17,0,0],"collapse":[42,null,null]},"A2+A3+A4+A5|G|KD45":{"cons":[17,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[45,null,null]},"A2+A3+A4+A5|G|S4":{"cons":[17,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[46,null,null]},"A2+A3+A4+A5|G|S5":{"cons":[17,null,null],"concl":[17,0,null],"box":[17,0,0],"collapse":[44,null,null]},"A1+A2+A3+A4+A5|S|K":{"cons":[11,null,null],"concl":[30,1,null],"box":[13,0,0],"collapse":[30,null,null]},"A1+A2+A3+A4+A5|S|D":{"cons":[11,null,null],"concl":[30,1,null],"box":[13,0,0],"collapse":[30,null,null]},"A1+A2+A3+A4+A5|S|T":{"cons":[11,null,null],"concl":[13,0,null],"box":[13,0,0],"collapse":[13,null,null]},"A1+A2+A3+A4+A5|S|B":{"cons":[11,null,null],"concl":null,"box":null,"collapse":null},"A1+A2+A3+A4+A5|S|K4":{"cons":[11,null,null],"concl":[30,1,null],"box":[13,0,0],"collapse":[30,null,null]},"A1+A2+A3+A4+A5|S|KB":{"cons":[11,null,null],"concl":null,"box":null,"collapse":null},"A1+A2+A3+A4+A5|S|KD45":{"cons":[11,null,null],"concl":[30,1,null],"box":null,"collapse":[30,null,null]},"A1+A2+A3+A4+A5|S|S4":{"cons":[11,null,null],"concl":[13,0,null],"box":[13,0,0],"collapse":[13,null,null]},"A1+A2+A3+A4+A5|S|S5":{"cons":[11,null,null],"concl":null,"box":null,"collapse":null},"A1+A2+A3+A4+A5|G|K":"X","A1+A2+A3+A4+A5|G|D":"X","A1+A2+A3+A4+A5|G|T":"X","A1+A2+A3+A4+A5|G|B":"X","A1+A2+A3+A4+A5|G|K4":"X","A1+A2+A3+A4+A5|G|KB":"X","A1+A2+A3+A4+A5|G|KD45":"X","A1+A2+A3+A4+A5|G|S4":"X","A1+A2+A3+A4+A5|G|S5":"X"}}'''
SHA = '91c8ed5b34cf1bf7139b5f6c66ac59e67a01c3a2ca013d5230c1cc754ac66a1b'
LEAN = r'''/- Varying-domain (actualist) shallow embedding: E x w = x exists at w.
   Individual quantifiers inside entailment, NE and the conclusion are guarded by E;
   property quantifiers range over all D → W → Prop (possibilist). Domains may be empty. -/
namespace OntoS
variable {W D : Type}
abbrev Prp (W D : Type) := D → W → Prop
def box (R : W → W → Prop) (p : W → Prop) (w : W) : Prop := ∀ v, R w v → p v
def neg (φ : Prp W D) : Prp W D := fun x w => ¬ φ x w
def entails (E : Prp W D) (R : W → W → Prop) (φ ψ : Prp W D) (w : W) : Prop :=
  ∀ v, R w v → ∀ x, E x v → φ x v → ψ x v
def essG (E : Prp W D) (R : W → W → Prop) (φ : Prp W D) (x : D) (w : W) : Prop :=
  ∀ ψ : Prp W D, ψ x w → entails E R φ ψ w
def essS (E : Prp W D) (R : W → W → Prop) (φ : Prp W D) (x : D) (w : W) : Prop :=
  φ x w ∧ essG E R φ x w
def NE (E : Prp W D) (R : W → W → Prop) (ess : Prp W D → D → W → Prop) : Prp W D :=
  fun x w => ∀ φ, ess φ x w → ∀ v, R w v → ∃ y, E y v ∧ φ y v
def God (Pos : Prp W D → W → Prop) : Prp W D := fun x w => ∀ φ, Pos φ w → φ x w
def ExG (E : Prp W D) (Pos : Prp W D → W → Prop) (w : W) : Prop := ∃ x, E x w ∧ God Pos x w
def A1a (Pos : Prp W D → W → Prop) : Prop := ∀ φ w, Pos (neg φ) w → ¬ Pos φ w
def A1b (Pos : Prp W D → W → Prop) : Prop := ∀ φ w, ¬ Pos φ w → Pos (neg φ) w
def A2 (E : Prp W D) (R : W → W → Prop) (Pos : Prp W D → W → Prop) : Prop :=
  ∀ φ ψ w, Pos φ w → entails E R φ ψ w → Pos ψ w
def A3 (Pos : Prp W D → W → Prop) : Prop := ∀ w, Pos (God Pos) w
def A5 (Pos : Prp W D → W → Prop) (N : Prp W D) : Prop := ∀ w, Pos N w

section
variable {E : Prp W D} {R : W → W → Prop} {Pos : Prp W D → W → Prop}

/-- Only the exclusion half A1a is used; seriality comes from any globally positive N. -/
theorem serial (h1 : A1a Pos) (h2 : A2 E R Pos) {N : Prp W D} (h5 : A5 Pos N) (w : W) :
    ∃ v, R w v :=
  Classical.byContradiction fun hn =>
    h1 N w (h2 N (neg N) w (h5 w) (fun v hv => absurd ⟨v, hv⟩ hn)) (h5 w)

theorem godel1970_inconsistent (h1 : A1a Pos) (h2 : A2 E R Pos)
    (h5 : A5 Pos (NE E R (essG E R))) (w : W) : False := by
  have empty_ess : ∀ (x : D) (u : W), essG E R (fun _ _ => False) x u :=
    fun _ _ _ _ _ _ _ _ h => False.elim h
  have noNE : ∀ u, (∃ v, R u v) → ∀ x, ¬ NE E R (essG E R) x u := by
    intro u ⟨v, hv⟩ x h
    obtain ⟨_, _, hy⟩ := h _ (empty_ess x u) v hv
    exact hy
  have hent : entails E R (NE E R (essG E R)) (neg (NE E R (essG E R))) w :=
    fun u hu x _ hx => absurd hx (noNE u (serial h1 h2 h5 u) x)
  exact h1 _ w (h2 _ _ w (h5 w) hent) (h5 w)

theorem godel1970_no_model (h1 : A1a Pos) (h2 : A2 E R Pos)
    (h5 : A5 Pos (NE E R (essG E R))) : ¬ Nonempty W := fun ⟨w⟩ => godel1970_inconsistent h1 h2 h5 w

/-- T1: positive properties are possibly exemplified by an existent. -/
theorem T1 (h1 : A1a Pos) (h2 : A2 E R Pos) {φ : Prp W D} {w : W} (hp : Pos φ w) :
    ∃ v, R w v ∧ ∃ x, E x v ∧ φ x v := by
  apply Classical.byContradiction
  intro hn
  have hent : entails E R φ (neg φ) w := fun v hv x he hx _ => hn ⟨v, hv, x, he, hx⟩
  exact h1 φ w (h2 _ _ w hp hent) hp

theorem haec_ess (x : D) (v : W) : essS E R (fun y u => y = x ∧ u = v) x v :=
  ⟨⟨rfl, rfl⟩, fun ψ hψ u _ y _ hy => by
    obtain ⟨h1, h2⟩ := hy
    subst h1; subst h2; exact hψ⟩

theorem NE_isolated {x : D} {v : W} (hne : NE E R (essS E R) x v) (u : W) (hu : R v u) :
    u = v := by
  obtain ⟨y, _, hy⟩ := hne _ (haec_ess x v) u hu
  exact hy.2

theorem A125_isolated_succ (h1 : A1a Pos) (h2 : A2 E R Pos) (h5 : A5 Pos (NE E R (essS E R)))
    (w : W) : ∃ v, R w v ∧ ∀ u, R v u ↔ u = v := by
  obtain ⟨v, hv, x, _, hx⟩ := T1 h1 h2 (h5 w)
  refine ⟨v, hv, fun u => ⟨NE_isolated hx u, fun h => ?_⟩⟩
  subst h
  obtain ⟨t, ht⟩ := serial h1 h2 h5 u
  have e := NE_isolated hx t ht
  subst e
  exact ht

theorem A125_sym_iso (hsym : ∀ a b, R a b → R b a) (h1 : A1a Pos) (h2 : A2 E R Pos)
    (h5 : A5 Pos (NE E R (essS E R))) (w : W) : ∀ v, R w v ↔ v = w := by
  obtain ⟨v, hv, hiso⟩ := A125_isolated_succ h1 h2 h5 w
  have e : w = v := (hiso w).mp (hsym w v hv)
  subst e
  exact hiso

theorem A125_sym_collapse (hsym : ∀ a b, R a b → R b a) (h1 : A1a Pos) (h2 : A2 E R Pos)
    (h5 : A5 Pos (NE E R (essS E R))) (Q : W → Prop) (w : W) (hQ : Q w) : box R Q w :=
  fun v hv => ((A125_sym_iso hsym h1 h2 h5 w v).mp hv) ▸ hQ

theorem A1235_sym_god (hsym : ∀ a b, R a b → R b a) (h1 : A1a Pos) (h2 : A2 E R Pos)
    (h3 : A3 Pos) (h5 : A5 Pos (NE E R (essS E R))) (w : W) :
    ExG E Pos w ∧ box R (ExG E Pos) w := by
  have g : ∀ t : W, ExG E Pos t := fun t => by
    obtain ⟨v, hv, x, he, hx⟩ := T1 h1 h2 (h3 t)
    have e := (A125_sym_iso hsym h1 h2 h5 t v).mp hv
    subst e
    exact ⟨x, he, hx⟩
  exact ⟨g w, fun u _ => g u⟩

theorem A1235_euclid_box (heuc : ∀ a b c, R a b → R a c → R b c) (h1 : A1a Pos)
    (h2 : A2 E R Pos) (h3 : A3 Pos) (h5 : A5 Pos (NE E R (essS E R))) (w : W) :
    box R (ExG E Pos) w := by
  obtain ⟨v0, hv0, hiso⟩ := A125_isolated_succ h1 h2 h5 w
  have only : ∀ u, R w u → u = v0 := fun u hu => (hiso u).mp (heuc w v0 u hv0 hu)
  intro u hu
  obtain ⟨v, hv, x, he, hx⟩ := T1 h1 h2 (h3 w)
  have e1 := only u hu
  have e2 := only v hv
  subst e1; subst e2
  exact ⟨x, he, hx⟩
end

/-- With E := everything, every varying-domain notion is definitionally the constant-domain one. -/
theorem entails_top (R : W → W → Prop) (φ ψ : Prp W D) (w : W) :
    entails (fun _ _ => True) R φ ψ w ↔ ∀ v, R w v → ∀ x, φ x v → ψ x v :=
  ⟨fun h v hv x hx => h v hv x trivial hx, fun h v hv x _ hx => h v hv x hx⟩
end OntoS
#print axioms OntoS.godel1970_no_model
#print axioms OntoS.T1
#print axioms OntoS.haec_ess
#print axioms OntoS.A125_sym_collapse
#print axioms OntoS.A1235_sym_god
#print axioms OntoS.A1235_euclid_box
#print axioms OntoS.serial
#print axioms OntoS.entails_top
'''
import json, hashlib, itertools, os, re, shutil, subprocess
D = json.loads(DATA)
print("sha256", hashlib.sha256(DATA.encode()).hexdigest())
assert hashlib.sha256(DATA.encode()).hexdigest() == SHA
MODELS, CELLS = D["models"], D["cells"]
# extra named model: universal 2-world frame, 1 individual, every property positive at both worlds
ALLPOS = [2, 1, [[0, 0], [0, 1], [1, 0], [1, 1]], [[0, 1, 2, 3], [0, 1, 2, 3]]]
MODELS = MODELS + [ALLPOS]; IALL = len(MODELS) - 1
CLASSES = {"K": [], "D": ["serial"], "T": ["refl"], "B": ["refl", "sym"], "K4": ["trans"],
           "KB": ["sym"], "KD45": ["serial", "trans", "eucl"], "S4": ["refl", "trans"],
           "S5": ["refl", "sym", "trans"]}
SYM = ["B", "KB", "S5"]
GOALS = ["cons", "concl", "box", "collapse"]

def evaluate(M, E):
    """Varying-domain (actualist) semantics; E bitmask, bit x*n+w = x exists at w (E = all gives
    constant domains). A1a: no positive complementary pair; A1b: phi or its complement positive."""
    n, m, Rl, pos = M
    R = {tuple(e) for e in Rl}
    succ = [[v for v in range(n) if (w, v) in R] for w in range(n)]
    P = 1 << (n * m); full = P - 1
    has = lambda f, x, w: (f >> (x * n + w)) & 1 == 1
    pos = [set(p) for p in pos]
    def ent(f, g, w):
        return all(not has(E, x, v) or not has(f, x, v) or has(g, x, v) for v in succ[w] for x in range(m))
    def essGo(f, x, w):
        return all(ent(f, g, w) for g in range(P) if has(g, x, w))
    essS = lambda f, x, w: has(f, x, w) and essGo(f, x, w)
    def NEof(es):
        return sum(1 << (x * n + w) for x in range(m) for w in range(n)
                   if all(any(has(E, y, v) and has(f, y, v) for y in range(m))
                          for f in range(P) if es(f, x, w) for v in succ[w]))
    NES, NEG = NEof(essS), NEof(essGo)
    God = sum(1 << (x * n + w) for x in range(m) for w in range(n) if all(has(f, x, w) for f in pos[w]))
    ok = dict(A1a=True, A1b=True, A2=True, A3=True, A4=True, A5S=True, A5G=True)
    for w in range(n):
        for f in range(P):
            a = f in pos[w]; c = (full ^ f) in pos[w]
            if a and c: ok["A1a"] = False
            if not a and not c: ok["A1b"] = False
            if a and not all(g in pos[w] for g in range(P) if ent(f, g, w)): ok["A2"] = False
            if a and not all(f in pos[v] for v in succ[w]): ok["A4"] = False
        if God not in pos[w]: ok["A3"] = False
        if NES not in pos[w]: ok["A5S"] = False
        if NEG not in pos[w]: ok["A5G"] = False
    W = range(n)
    pr = dict(refl=all((w, w) in R for w in W), sym=all((v, w) in R for (w, v) in R),
              trans=all((w, u) in R for (w, v) in R for (a, u) in R if a == v),
              serial=all(succ[w] for w in W),
              eucl=all((v, u) in R for (w, v) in R for (a, u) in R if a == w))
    godAt = lambda w: any(has(God, x, w) and has(E, x, w) for x in range(m))
    return pr, ok, R, succ, godAt

def holds(ok, sub, ess):
    return all(ok["A5" + ess if a == "A5" else a] for a in sub)

# Lean theorems (hypotheses use A1a only); a cell is proved iff its axioms contain the hypotheses
THMS = [({"A1a", "A2", "A5"}, "G", None, ["INCONS"], "godel1970_no_model"),
        ({"A1a", "A2", "A5"}, "S", SYM, ["collapse"], "A125_sym_collapse"),
        ({"A1a", "A2", "A3", "A5"}, "S", SYM, ["concl", "box"], "A1235_sym_god"),
        ({"A1a", "A2", "A3", "A5"}, "S", ["KD45"], ["box"], "A1235_euclid_box")]
def proof(ax, ess, cls, g):
    for hyp, e, cl, gs, nm in THMS:
        if hyp <= ax and e == ess and (cl is None or cls in cl) and (g in gs or "INCONS" in gs):
            return nm
    return None

AX = ["A1a", "A1b", "A2", "A3", "A4", "A5"]
TABLE = {}; nmodel = nlean = nincons = nall = 0
cache = {}
def ev(mi):
    if mi not in cache:
        M = MODELS[mi]; cache[mi] = evaluate(M, (1 << (M[0] * M[1])) - 1)
    return cache[mi]
for r in range(7):
    for c in itertools.combinations(AX, r):
        ax = set(c)
        for ess in (["S", "G"] if "A5" in ax else ["S"]):
            for cls in CLASSES:
                key = "+".join(c) or "-"
                incons = proof(ax, ess, cls, "cons") == "godel1970_no_model"
                row = {}
                # K3 parent cell: replace A1a/A1b by bundled A1 (its models satisfy both halves)
                k3 = [a for a in ["A1", "A2", "A3", "A4", "A5"] if (a in ax) or (a == "A1" and ax & {"A1a", "A1b"})]
                parent = CELLS[("+".join(k3) or "-") + "|" + ess + "|" + cls]
                for g in GOALS:
                    if incons:
                        row[g] = "L:godel1970_no_model"; nincons += 1; continue
                    nm = proof(ax, ess, cls, g)
                    if nm:
                        row[g] = "L:" + nm; nlean += 1; continue
                    cert = None if parent == "X" else parent[g]
                    if cert is None:
                        assert "A1a" not in ax, ("needs proof", key, ess, cls, g)
                        mi, w, v = IALL, 0, 1; nall += 1
                    else:
                        mi, w, v = cert
                    pr, ok, R, succ, godAt = ev(mi)
                    assert holds(ok, ax, ess), ("axioms", key, ess, cls, g)
                    assert all(pr[q] for q in CLASSES[cls]), ("class", key, ess, cls, g)
                    if g == "concl": assert not godAt(w), key
                    if g == "box": assert v in succ[w] and not godAt(v), key
                    if g == "collapse": assert any(a != b for (a, b) in R), key
                    row[g] = "M:%d" % mi; nmodel += 1
                TABLE[key + "|" + ess + "|" + cls] = row
assert len(TABLE) == 64 * 9 + 32 * 9  # Goedel essence only where A5 present

# stated pattern, cell by cell
for k, row in TABLE.items():
    sub, ess, cls = k.split("|"); ax = set() if sub == "-" else set(sub.split("+"))
    L = lambda g: row[g].startswith("L:")
    if ess == "G":
        assert L("cons") == ({"A1a", "A2", "A5"} <= ax), k
        if L("cons"): continue
    assert not L("cons"), k
    assert L("concl") == ({"A1a", "A2", "A3", "A5"} <= ax and ess == "S" and cls in SYM), k
    assert L("box") == ({"A1a", "A2", "A3", "A5"} <= ax and ess == "S" and cls in SYM + ["KD45"]), k
    assert L("collapse") == ({"A1a", "A2", "A5"} <= ax and ess == "S" and cls in SYM), k
# A1b is never needed: dropping A1b never changes a row's proof/model status
for k, row in TABLE.items():
    sub, ess, cls = k.split("|")
    if "A1b" in sub.split("+"):
        s2 = "+".join(a for a in sub.split("+") if a != "A1b") or "-"
        r2 = TABLE[s2 + "|" + ess + "|" + cls]
        assert all(row[g][0] == r2[g][0] for g in GOALS), k
blob = json.dumps(TABLE, sort_keys=True)
print("table sha256", hashlib.sha256(blob.encode()).hexdigest())
assert hashlib.sha256(blob.encode()).hexdigest() == "eb8f629f172fc54488a55f7660691ff65c3598a8d5a1252fa5d51678e6e4eab3"

# sanity sweep: every pool model x every existence pattern E against every Lean theorem
nvar = nsat = 0
for M in MODELS:
    n, m = M[0], M[1]
    for E in range(1 << (n * m)):
        pr, ok, R, succ, godAt = evaluate(M, E); nvar += 1
        assert not (ok["A1a"] and ok["A2"] and ok["A5G"]), ("godel model", M, E)
        for hyp, ess, cl, gs, nm in THMS[1:]:
            if not holds(ok, hyp, ess): continue
            for cls in cl:
                if not all(pr[q] for q in CLASSES[cls]): continue
                nsat += 1
                for w in range(n):
                    if "concl" in gs: assert godAt(w)
                    if "box" in gs: assert all(godAt(v) for v in succ[w])
                    if "collapse" in gs: assert all(v == w for v in succ[w])

lean = shutil.which("lean") or os.path.expanduser("~/.elan/bin/lean")
assert "sorry" not in LEAN and not re.search(r"^\s*axiom\s", LEAN, re.M)
assert "A1 Pos" not in LEAN  # only the split halves are defined
p = subprocess.run([lean, "--stdin"], input=LEAN, capture_output=True, text=True, timeout=110)
print(p.stdout, p.stderr)
assert p.returncode == 0 and "error" not in p.stdout
STD = {"propext", "Classical.choice", "Quot.sound"}
names = re.findall(r"'OntoS\.(\w+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", p.stdout)
assert {nm for nm, _ in names} == {"godel1970_no_model", "T1", "haec_ess", "A125_sym_collapse",
                                    "A1235_sym_god", "A1235_euclid_box", "serial", "entails_top"}, names
for nm, ax in names:
    assert {a.strip() for a in ax.split(",") if a.strip()} <= STD, (nm, ax)
print("PASS: split-A1 full-property Scott table, %d cells: %d model outcomes (%d by all-positive model), "
      "%d Lean outcomes, %d inconsistent-cell outcomes; sweep %d (model,E) pairs, %d theorem instances"
      % (len(TABLE), nmodel, nall, nlean, nincons, nvar, nsat))
