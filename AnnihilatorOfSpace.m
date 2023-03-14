

/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given an algebra A, and a subspace W with a prescribed basis as a list of vectors,  determine ann W.                                       +
+ The inputs are A, which must be axial, or a tensor which gives algebra multiplication. The basis, bas, of W, can be ordinary vectors.     +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/ 

AnnihilatorOfSpace:=function(A,bas)
	tens:=[];
	d:=Dimension(A);
	V:=VectorSpace(Rationals(),d);
	basmat:=Matrix(Rationals(),[Eltseq(A.i):i in [1..d]]);
	for i:=1 to d do 
		for j:=1 to d do 
			if i le j then
				Append(~tens, Solution(basmat,V!Eltseq(A.i*A.j)));
			end if;
		end for;
	end for;
/*here we can as well just input the tensor.*/
	
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
		return Solution(Transpose(M),big_vec);

end function;
