/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given an idempotent a in an axial algebra, we wish to find out if a satisfies a fusion law.       +
+                                                                                                   +
+ FindFusion AxlAlgxVectSpace-->2^X, where X:=Spec(a).                                              +
+                                                                                                   +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
FindFusionLaw:=function(A,V,a) /*V is a subspace which could be A.*/
	eigs:=Eigenvalues(AdMatInSubAlg(A,V,a));
	fus:=[* *];
	eigs:=SetToSequence(eigs);
	evals:=[eigs[i][1]:i in [1..#eigs]];
	mults:=[eigs[i][2]:i in [1..#eigs]];
	ord_eigs:=[1/1]; 
	ord_mults:=[x[2]] where x is [y:y in eigs|y[1] eq 1][1];
	if 0 in evals then
		Append(~ord_eigs,RationalField()!0);
		ind:=Index(eigs,x) where x is [y:y in eigs|y[1] eq 0][1];
		Append(~ord_mults,mults[ind]);
	end if;
	for i:=1 to #evals do
		if evals[i] notin ord_eigs then
			Append(~ord_eigs,evals[i]);
			Append(~ord_mults,mults[i]);
		end if;
	end for;
	for j:=1 to #evals do
    		for k:=j to #evals do
        	ind:=IntegerRing()!(((j-1)/2)*(2*#evals-j+2))+k-j+1;
        	fus[ind]:=[*<ord_eigs[j],ord_eigs[k]>,[ ]*];
    		end for;
	end for;/*at this stage fus will have <<\mu,\lambda>,[]> for each fusion rule.*/
	m:=Dimension(V);
	F:=BaseField(A);
	W:=VectorSpace(F,m);
	bas_mat:=Matrix(F,[Eltseq(V.i):i in [1..m]]);
	Id:=IdentityMatrix(F,m);
	ad_mat:=AdMatInSubAlg(A,V,a);
	Projs:=[];
	for i:=1 to #ord_eigs do
		Append(~Projs,&*[(ad_mat-ord_eigs[j]*Id)/(ord_eigs[i]-ord_eigs[j]):j in [1..#eigs]|j ne i]);
	end for;
	for i:=1 to m do
		w:=W.i;
		splits:=[w*Projs[t]:t in [1..#evals]];
		for j:=1 to #evals do
			for k:=j to #evals do
				prod:=(ToBigVec(A,V,splits[j]))*(ToBigVec(A,V,splits[k]));
				prod_w:=A`W!Eltseq(prod);
				prod_short:=Solution(bas_mat,prod_w);
				for s:=1 to #Projs do
					if prod_short*Projs[s] ne W!0 then
						ind:=IntegerRing()!(((j-1)/2)*(2*#evals-j+2))+k-j+1;
						if ord_eigs[s] notin fus[ind][2] then
						       Append(~fus[ind][2],ord_eigs[s]);  
						end if;
					end if;
				end for;
			end for;
		end for;
	end for;		
	return fus;
end function;

