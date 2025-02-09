# Hochschild-cohomology
Hochschild cohomology of Group Extensions of Truncated Four Generator Polynomial Rings

--kk = QQ 
kk = ZZ/1801
R = kk[q_(0,0)..q_(3,3)]
I = ideal(
    q_(0,0) + 1,
    q_(1,1) + 1,
    q_(2,2) + 1,
    q_(3,3) + 1,
    q_(0,1) * q_(1,0) - 1,
    q_(0,2) * q_(2,0) - 1,
    q_(0,3) * q_(3,0) - 1,
    q_(1,2) * q_(2,1) - 1,
    q_(1,3) * q_(3,1) - 1,
    q_(2,3) * q_(3,2) - 1
)
S = R / I
b = select((0,0,0,0)..(2,2,2,2),x -> x_0 + x_1 + x_2 + x_3 == 2 )
a = select((0,0,0,0)..(1,1,1,1), x -> x_0+x_1+x_2+x_3 == 2)
b1 = toList(apply(b, i -> toList(i)))
a1 = toList(apply(a, i -> toList(i)))
g = flatten(apply(b1, i -> apply(a1, j -> i -j)))
g1 = unique(g)
p = flatten(toList(apply(0..#b1-1, i -> apply( 0..#a1-1, j -> (b1_i, a1_j)))))
p1 = join(apply(0..#p-1, i -> p_i))
ba = toList(apply(0..#g1-1, k -> (select(p1, (i,j) -> i-j ==g1_k))))
ba1 = toList(apply(ba, i -> toList(i)))
bag = apply(0..#ba - 1, j -> apply(0..#(ba_j)-1, i -> (((ba_j)_i)_0, ((ba_j)_i)_1, ((ba_j)_i)_0 - ((ba_j)_i)_1)))
bag1 = apply(0..#bag-1, i -> (#bag_i, g1_i))


four = set(0..3)
-- for every g calculate using the formula
z = apply(g1, a -> apply(0..3, i -> if a_i != -1 then (-1)^(a_i) * product(toList(four), j -> (-q_(j,i))^(a_j)) - 1 else 0))
-- when the entry is -1 it gives 0, so eliminate the case
znoZeroes = apply(z,u->select(u,x->x != 0))
-- exponents of each q_ij
z1 = apply(0..#znoZeroes-1, i ->znoZeroes_i/exponents) 
-- deleting this case as this is for 1
z1nosetzeroes = apply(0..#z1-1, i -> apply(0..#(z1_i)-1, j -> delete({0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},z1_i_j)))
z1new = apply(0..#z1nosetzeroes - 1, i -> flatten(z1nosetzeroes_i))
-- converting those into matrices
map(ZZ^4,ZZ^4,(i,j)->(((z1new_0)_0)_(4*i+j)))
z1matrix = apply(0..#z1new-1, l ->(apply(0..#z1new_l -1, k -> map(ZZ^4,ZZ^4,(i,j)->(((z1new_l)_k)_(4*i+j))))))
--- mat - trans mat
mat1 = apply(0..#z1matrix - 1, i -> apply(0..#z1matrix_i - 1, j -> z1matrix_i_j - transpose(z1matrix_i_j)))
mat1up = apply(0..#mat1 - 1, l -> apply(0..#mat1_l -1 , k -> matrix(toList(apply(0..3, i -> toList apply(0..3, j -> if j < i then 0 else ((mat1_l)_k)_(i,j)))))))
--only right upper entries
rightUpperTriangularEntries = M -> select(flatten(for i to numrows M - 1 list for j to numcols M - 1 list if j > i then M_(i, j)), x -> x =!= null)
rute = apply(0..#mat1up-1, i -> apply(0..#(mat1up_i) -1 , j -> rightUpperTriangularEntries(mat1up_i_j)))
rowmatrix = apply(0..#rute - 1, i -> apply(0..#rute_i -1, j -> matrix{(rute_i)_j}))
cm = apply(0..#rowmatrix - 1, i -> apply(0..#rowmatrix_i -1, j -> transpose(rowmatrix_i_j)))
--find all submodules and see how many there are of each rank.  

concatMatrices = (seq) -> (
    n = #seq;
    if n == 0 then (
        matrix{{},{},{},{},{},{}}
    ) else (
        result = seq#0;
        for i from 1 to n-1 do (
            result = result | seq#i;
        );
        result
    )
)

concm = apply(0..#cm-1, i -> concatMatrices(toList(cm_i)))
im = apply(0..#concm - 1, i -> mingens image(concm_i))

conmat = (A, B) -> mingens image (A | B)
newList = ()
n = #im
for i from 0 to n-1 do (
    for j from i to n-1 do (
        if i != j then (
            c = conmat(im_i, im_j);
            if not isMember(c, im) then (
                newList = append(newList, c);
            )
        )
    )
)
newList = unique(newList)
newList = join(im,newList)
#newList
additionalNewList = newList
while (#additionalNewList > 0) do ((
    additionalNewList = ();
    for k from 0 to #newList-1 do (
        for m from k+1 to #newList-1 do (
            
                c = conmat(newList#k, newList#m);
k;
m;

                if not isMember(c, newList) then (
                    additionalNewList = append(additionalNewList, c);
                )
            
        )
    );
);
    additionalNewList = unique(additionalNewList);
#additionalNewList;
    newList = join(newList, additionalNewList);
    newList = unique(newList);

);
newList = unique(newList);
#newList
#(select(0..#newList-1, i -> rank(newList_i) ==6))
r = apply(0..#newList-1, i -> rank(newList_i));
y = tally(toList(r))
r0 = select(newList, i -> rank(i) == 0);
r2 = select(newList, i -> rank(i) == 2);
r3 = select(newList, i -> rank(i) == 3);
r4 = select(newList, i -> rank(i) == 4);
r5 = select(newList, i -> rank(i) == 5);
r6 = select(newList, i -> rank(i) == 6);
m = select(newList, i -> rank(i) ==6);
el = apply(0..#m-1, i -> ZZ^6/image(m_i));
d = apply(0..#m-1, i -> det(m_i));
tally(toList(d))






loadPackage"InvariantRing"
toSt = x -> (toString(x_0+1)|toString(x_1+1)|toString(x_2+1)|toString(x_3+1))
s4 = permutations 4 / toSt / permutationMatrix
b = {{1,2}, {1,3}, {1,4}, {2,3}, {2,4}, {3,4}}
--find the position of {i,j} in b
fp = (i, j) -> (
    if i > j then (i, j) = (j, i); -- Ensure i < j
    for k from 0 to 5 do (
        if b_k == {i, j} then return k
    );
    error "Position not found"
)
con = (permMatrix) -> (
    M = mutableMatrix(matrix table(6, 6, (i, j) -> 0)); -- initialize a 6x6 zero matrix
    for k from 0 to 5 do (
        i = (b_k)_0;
        j = (b_k)_1;
        newI = 0;
        newJ = 0;
        for l from 0 to 3 do (
            if permMatrix_(i-1, l) == 1 then newI = l+1;
            if permMatrix_(j-1, l) == 1 then newJ = l+1;
        );
        sign = 1;
        if newI > newJ then (
            temp = newI;
            newI = newJ;
            newJ = temp;
            sign = -1;
        );
        newPos = fp(newI, newJ);
        M_(newPos, k) = sign;
    );
    matrix M
)
all6 = apply(s4, i -> con(i))
L = apply(0..23, i -> apply(0..23, j ->  (all6)_i * (all6)_j))
#unique flatten L
o = (M -> select(1..24, j -> M^j ==all6_0))
apply(all6,o)
tally(apply(all6,o))
cond = () -> (
    for p in all6 do (
        for i from 0 to #r2 - 1 do (
            for j from i+1 to #r2 - 1 do (
                A = r2_i;
                B = r2_j;
                if mingens image (p * A) == mingens image B then (
                    return true;
                )
            )
        )
    );
    return false
)
orbitReps = (r -> (filteredList = new MutableList;
filteredList = {};
excluded = new MutableList;
excluded = {};
for i from 0 to #r - 1 do (
    A = r_i;
    shouldExcludeA = false;
    for p in all6 do (
        for j from 0 to #r - 1 do (
            if i != j then (
                B = r_j;
                if mingens image (p * A) == mingens image B then (
                    if not isMember(B, excluded) then (
                       excluded =  append(excluded, B);
                    );
                    shouldExcludeA = true;
                );
            );
        );
    );
    if not isMember(A, excluded) then (
        filteredList = append(filteredList, A);
    );
);
resultList = toList filteredList))
resultList
or0 = orbitReps(r0);
or2 = orbitReps(r2);
or3 = orbitReps(r3);
or4 = orbitReps(r4);
or5 = orbitReps(r5);
or6 = orbitReps(r6);
--the image of matrix A is inside the image of matrix B
s = (A, B) -> (mingens (image A + image B) == mingens image B)
--or2im = apply(0..#or2-1,i -> select(0..#im-1, j -> s(im_j,or2_i)))
--or2Im1 = toList(apply(or2im, i -> toList(i)))
--or2g1 = apply(or2Im1, i -> g1_i)
--orba1 = apply(or2Im1, i -> ba1_i)
--orbag = apply(orIm1, i -> bag_i)
--oreq = apply(orIm1, i -> z_i)
--numbag = apply(0..#orbag-1,j ->sum(apply(orbag_j, i -> #(i))))

calculateOrIm = (orSeq, im, bag) -> (
        orI = apply(0..#orSeq-1, i -> select(0..#im-1, j -> s(im_j, orSeq_i)));
    orIm = toList(apply(orI, i -> toList(i)));
    org1 = apply(orIm, i -> g1_i);
    orba1 = apply(orIm, i -> ba1_i);
    orBag = apply(orIm, i -> bag_i);
    oreq = apply(orIm, i -> z_i);
    numBag = apply(0..#orBag-1, j -> sum(apply(orBag_j, i -> #(i))));
    numBag
);
or0im = calculateOrIm(or0, im, bag)
or2im = calculateOrIm(or2, im, bag)
or3im = calculateOrIm(or3, im, bag)
or4im = calculateOrIm(or4, im, bag)
or5im = calculateOrIm(or5, im, bag)
or6im = calculateOrIm(or6, im, bag)


