
/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given an algebra A, determine if it is a unital algebra.                                                                                  +
+                                                                                                                                           +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/ 

HasIdentityAlg:=function(A)
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
	k:=1;
	
	rows:=[];
	vecs:=[];
	sols:=[];
	
	for k:=1 to d do

		for l:=1 to d do
		       	row:=[];

			for i:=1 to d do
			
				ii:=Minimum({i,k});jj:=Maximum({i,k});
				Append(~row,tens[IntegerRing()!((ii-1)/2*(2*d+2-ii))+jj-ii+1][l]); 
			end for;
			Append(~rows,row);	

		end for;
			vec:=Zero(V);
			vec[k]:=1;
		Append(~vecs,vec);
	
		end for;
		
		big_vec:=&cat[Eltseq(x):x in vecs];
		big_vec:=Vector(Rationals(),big_vec);	
//		print #vecs,#rows;
//		print #rows[2];
		return IsConsistent(Transpose(Matrix(Rationals(),rows)),big_vec);

end function;
