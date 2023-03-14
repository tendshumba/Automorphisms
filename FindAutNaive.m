/*++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+This is the brute force approach to finding all the axes of Monster M(1/4,1/32).                 +
+                                                                                                 +
+												  +
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
FindAutNaive:=function(A);
	idemps:=FindAllIdempotents(A,A`W);
	try 
		if idemps eq "fail" then	
		return "fail";
		end if;
			idemps:=idemps;
			print "idempotents found";
	catch e
		axes:=[];
		for x in idemps do
			if Dimension(Eigenspace(AdMat(x),1)) eq 1 then
				if HasMonsterFusion(x) then
					Append(~axes,A!Eltseq(x));
				end if;
			end if;
		end for;
			known_axes:=&join[x:x in Axes(A)];
			known_axes:=[A!x:x in known_axes];
			new:=[x:x in axes| not x in known_axes];
			if #new eq 0 then
				print "nothing new";
			else
				print "new axes found";
			end if;
				return axes;
	
		return "fail";
	end try;
	end function;
