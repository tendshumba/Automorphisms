

/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+ Given a list lst:=[a,b,c,..] of axial algebra elements which are axes, decompose the parent alegbra A in terms of joint eigespace+
+ $A_{\lambda\,\mu,\\gamma}:=A_{\lambda}(a)\cap A_{\mu}(b)\cap A_{\gamma}(c).$                                                     +
+                                                                                                                                  +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
DecomposeToJointEigenspaces:=function(lst)
	decomps:=[* *];
	dims:=[];
	A:=Parent(lst[1]); /* why this must be really axial*/ 
	eigs:=[1,0,1/4,1/32];
	n:=#lst;
	combs:=[];
	ads:=[AdMat(lst[i]):i in [1..n]];
	Lst:=[[Eigenspace(ads[i],1):i in [1..n]],[Eigenspace(ads[i],0):i in [1..n]],[Eigenspace(ads[i],1/4):i in [1..n]],[Eigenspace(ads[i],1/32):i in [1..n]]];
	cart:=CartesianPower([1..4],n);
	for x in cart do 
		joint_space:=&meet[Lst[x[i]][i]:i in [1..n]];
		dim:=Dimension(joint_space);
		if not dim eq 0 then
			Append(~decomps,joint_space);
			Append(~dims,dim);
			Append(~combs,<[eigs[x[i]]:i in [1..n]],dim>);
			//printf("A_{%o %o %o} is %o-dimensional \n"),eigs[i] where i is 
		end if; 
	end for; 
	if &+[x:x in dims] eq Dimension(A) then;
		return decomps,combs;
	else
		//plus_a:=&+[Lst[i][1]:i in [1..3]];
		return decomps,combs; 
	end if;
end function; 
