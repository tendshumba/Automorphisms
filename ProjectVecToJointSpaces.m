
/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given a vector u, project it into a space V. This will assume that the algebra A containing u has a form  +
+ U.                                                                                                        +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
ProjectVecToJointSpaces:=function(u,lst,lst1) 
	A:=Parent(u);
        n:=Dimension(A);	
	F:=BaseField(A);
	eigs:=[1,0,1/4,1/32];
	ads:=[];
	for i:=1 to #lst do
		Append(~ads,AdMat(lst[i]));
	end for; 
	projs:=[];
	Id:=IdentityMatrix(F,n); 
	for i:=1 to #lst do
		ad:=ads[i];
		pj:=[];
		for j:=1 to 4 do
			proj:=&*[(ad-eigs[k]*Id)/(eigs[j]-eigs[k]):k in [1..4]|k ne j];
		 	Append(~pj,proj);
		end for;
		Append(~projs,pj);
		//Append(~projs,[&*[(ads[i]-eigs[k]*Id)/(eigs[k]-eigs[j]):j in [1..4]|j ne k]:k in [1..4]]);
	end for; 
	im:=A`W!Eltseq(u); 
	for i:=1 to #lst1 do
       		ind:=Index(eigs,lst1[i]); 
		//im*:=projs[i][ind];
		im:=im*(projs[i][ind]);
	end for;	
	return projs,A!im;
end function;
