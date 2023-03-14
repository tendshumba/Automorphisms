/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ This function takes an axial algebra A, and two lists, input, and images, of axial vectors which must be of the same length and ouputs    +
+ a boolean value as well as either a map in matrix form or a subalgebra if the map does not extend to the full space.                      +
+                                                                                                                                           +
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/

ExtendMapToAut:=function(A,input,images)
	/*(A,l1,l2)-->bool,vector space or matrix.*/
	dim:=Dimension(A);
	closed:=0;
	F:=BaseField(A);
	lst:=[A`W!Eltseq(input[i]):i in [1..#input]];
	ims:=images;
	if #lst ne # ims then
	      print "error, the lengths of the input and output lists must be  equal";
	      return "fail",_;
	end if;
	sub:=sub<A`W|lst>;
	if Dimension(sub) ne #lst then
		print "error warning, the input list is not independent";
		sub1:=sub<A`W|(A`W)!0>;
		lst1:=[];
		images1:=[];
		for i:=1 to #images do 
			if not A`W!Eltseq(input[i]) in sub1 then
				Append(~lst1,A`W!Eltseq(input[i]));
				Append(~images1,images[i]);
				sub1+:=sub<A`W|A`W!Eltseq(input[i])>;
			end if;
		end for;
		input:=[A!lst1[i]:i in [1..#lst1]];
		images:=images1;
		lst:=lst1;
		printf("dimension of sub is %o \n"),Dimension(sub);
		printf("the size of the maximaly independent set is %o\n"),#lst;
		ims:=images;
	end if;
	m:=1;
	if #lst eq dim then
		closed:=1;
	else
		m+:=1;
	end if;
	/*this deals with the obvious failures and an input list as long as the dimension. At this point independence has been established.*/
	if m eq 2 then
		current_inds:=[];
		current_inds[1]:=1;
		current_inds[2]:=#lst;
		for i:=current_inds[1] to current_inds[2] do
			for j:=i to current_inds[2] do
				w:=input[i]*input[j];
				ww:=A`W!Eltseq(w);
				if ww notin sub then
					Append(~lst,ww);
					Append(~ims,ims[i]*ims[j]);
					sub+:=sub<A`W|ww>;
				end if;
			end for;
		end for;
		if #lst eq dim then
			closed:=1;
		else
			subclosed:=1;
			for i:=current_inds[1] to #lst do
				for j:=current_inds[2]+1 to #lst do
					w:=(A!lst[i])*(A!lst[j]);
					ww:=A`W!Eltseq(w);
					if ww notin sub then
						subclosed:=0;
						m+:=1;
						break i;
					end if;
				end for;
			end for;
		end if;
			current_inds[1]:=current_inds[1]+1;
			current_inds[2]:=#lst;
		end if;
			printf("current dimension is %o \n"),#lst;
		while closed eq 0 do
			for i:=1 to #input do
				for j:=current_inds[1] to current_inds[2] do
					w:=(A!lst[i])*(A!lst[j]);
					ww:=A`W!Eltseq(w);
					if ww notin sub then
						Append(~lst,ww);
						Append(~ims,ims[i]*ims[j]);
						sub+:=sub<A`W|ww>;
					end if;
				end for;
			end for;
			if #lst eq dim then
				closed:=1;
			else
				subclosed:=1;
				for i:=current_inds[1] to #lst do
					for j:=current_inds[2]+1 to #lst do
						w:=(A!lst[i])*(A!lst[j]);
						ww:=A`W!Eltseq(w);
						if ww notin sub then
							Append(~lst,ww);
							Append(~ims,ims[i]*ims[j]);
							sub+:=sub<A`W|ww>; 
							subclosed:=0;
							m+:=1;
							break i;
						end if;
					end for;
				end for;
					if subclosed eq 1 then
						closed:=1;
					end if;
						
			end if;
			current_inds[1]:=current_inds[2]+1;
			current_inds[2]:=#lst;
			printf("current dimension is %o \n"),#lst;
		end while;
			printf("multiplication is now closed with minimum %o-closure \n"),m;
			if #lst lt dim then
				return "false",sub;
			end if;
			bas_mat:=Matrix(F,[Eltseq(lst[i]):i in [1..#lst]]);
			phi:=Matrix(F,[Eltseq(Solution(bas_mat,A`W!Eltseq(ims[i]))):i in [1..#ims]]);
			std_phi:=bas_mat^(-1)*phi*bas_mat;
			if std_phi eq IdentityMatrix(F,#lst) then
				return "true", std_phi;
			else
				//return IsAutomorphic(A,A`W,std_phi),std_phi;
				return "true",std_phi;

				/*this will be multiplicative by construction, we need only check that it is invertible;*/
			end if;
	end function;

