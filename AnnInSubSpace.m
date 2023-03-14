


/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given an algebra A, a subalgebra V, and a subspace W of V with a prescribed basis as a list of vectors,  determine ann W.                 +
+ The inputs are A, which must be axial, or a tensor which gives algebra multiplication. The basis, bas, of W, can be ordinary vectors.     +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/ 

AnnInSubSpace:=function(A,V,bas)
	tens:=[];
	d:=Dimension(V);
	W:=VectorSpace(Rationals(),Dimension(A));
	basmat:=Matrix(Rationals(),[Eltseq(V.i):i in [1..d]]);
	for i:=1 to d do 
		for j:=1 to d do 
			if i le j then
				Append(~tens, Solution(basmat,Vector(BaseField(A),Eltseq(A!Eltseq(V.i)*A!Eltseq(V.j)))));
			end if;
		end for;
	end for;
/*here we can as well just input the tensor.*/
	bas:=[Solution(basmat,Vector(BaseField(A),Eltseq(x))):x in bas];	
        m:=#bas;	
        M:=ZeroMatrix(Rationals(),m*d,d); 
	for k:=1 to m do

		for l:=1 to d do
		       	row:=[];

			for i:=1 to d do
				for j:=1 to d do 	
					ii:=Minimum({i,j});jj:=Maximum({i,j});
					M[d*(k-1)+l][i]+:=bas[k][j]*tens[IntegerRing()!((ii-1)/2*(2*d+2-ii))+jj-ii+1][l];
				end for; 
			end for;
		
		end for;
	
	end for;
		
		big_vec:=VectorSpace(Rationals(),d*m)!0;	
		_,sols:=Solution(Transpose(M),big_vec);
		bas_sols:=Basis(sols);
		sub_ann:=[&+[Eltseq(bas_sols[i])[j]*V.j:j in [1..d]]:i in [1..Dimension(sols)]];
		return sub<W|sub_ann>;
end function;
