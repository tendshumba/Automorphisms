/* Given an axial algebra A (partial or complete), return the list of orbits of axes that generate A. Thanks to Justin for this.*/
	Axes:=function(A)
	orbs:=Orbits(Group(A),A`GSet);
	phi:=A`GSet_to_axes;
	axis_orbits:=[{@A!(i@phi):i in o@}:o in orbs];
	return axis_orbits;
end function;
