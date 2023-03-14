
//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
// This function takes an automorphism phi of a subalgebra V of an axial algebra A and checks whether the         + 
// automorphism extends to an automorphism of the the module M of V under adjoint actions of V. Note here         +
//that V is just an ordinary space but A must be axial. Also, phi must be a dim(V)xdim(V) matrix over the base-   +
//field of A. We assume that it is indeed an automorphism and a check shall not be made.                          +
//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

ExtendAutToMod:=function(A,V,M,phi)
	n:=Dimension(A); k:=Dimension(V); m:=Dimension(M);
	//W:=VectorSpace(BaseField(A),n);
	F:=BaseField(A);
	V_onM:=[];
	for i:=1 to k do
	       Append(~V_onM,AdMatInSubAlg(A,M,A!V.i));
	end for;
 	/*we've set up the ad_vi matrices acting on M, where v_i is a basis for V.*/ 
	sols:=[* *]; /*initialise the solution list.*/
	B:=ZeroMatrix(F,k*m^2,m^2);
	count:=1; 
	for i:=1 to k do/*fixing some v_i.*/
		for j:=1 to m do /*fixing m_j.*/
			v_im_j:=V_onM[i][j];/* the entries of v_i*m_j are the values C_1,...,C_m.*/
			Mat_lhs:=ZeroMatrix(F,m,m*m);
			for l:=1 to m do /*this is the row number for the matrix lhs.*/
				for r:=1 to m do
				Mat_lhs[l][(r-1)*m+l]:=v_im_j[r];	
				end for;
			end for;
			//Mat_lhs; 
			Mat_rhs:=ZeroMatrix(F,m,m*m);
			vi_phi:=ToSmallVec(A,V,A!V.i)*phi;/* we get \mu_1,...,\mu_k.*/ 
			for l:=1 to m do /*row number of the mat, corresponding to the cols of (x_ij).*/
				for r:=1 to m do 
					coeff:=&+[vi_phi[t]*V_onM[t][r][l]:t in [1..k]];
					Mat_rhs[l][(j-1)*m+r]:=coeff;
				end for;
			end for;
			//Mat_rhs;
			syst:=Mat_lhs-Mat_rhs;
			for l:=1 to m do
				B[(count-1)*m+l]:=syst[l];
			end for;
			count+:=1; 
		end for;
	end for;
	print "the system of equations has been set up.\n";
	sol,space:=Solution(Transpose(B),Vector(F,[0*t:t in [1..m*m*k]]));
	if Dimension(space) eq 0 then
		return false,_;
	else
		return true,space;
	end if; 
end function;	

