newPackage("SurfacesInP4",
    Authors => {{Name => "David Eisenbud", 
                 Email => "de@msri.org", 
                 HomePage => "http://www.msri.org/~de"},
                {Name => "Mike Stillman", 
                 Email => "mike@math.cornell.edu", 
                 HomePage => "http://pi.math.cornell.edu/~mike"}},
    Version => "0.1",
    Date => "January 5, 2021",
    Headline => "Smooth surfaces in P4, not of general type",
    AuxiliaryFiles => true,
    DebuggingMode => true
    )

export {}



end--
-* Documentation section *-
beginDocumentation()

doc ///
Key
  SurfacesInP4
Headline
Description
  Text
  Tree
  Example
  CannedExample
Acknowledgement
Contributors
References
Caveat
SeeAlso
Subnodes
///

doc ///
Key
Headline
Usage
Inputs
Outputs
Consequences
  Item
Description
  Text
  Example
  CannedExample
  Code
  Pre
ExampleFiles
Contributors
References
Caveat
SeeAlso
///

-* Test section *-
TEST /// -* [insert short title for this test] *-
-- test code and assertions here
-- may have as many TEST sections as needed
///

end--

-* Development section *-
restart
debug needsPackage "SurfacesInP4"
check "SurfacesInP4"

uninstallPackage "SurfacesInP4"
restart
installPackage "SurfacesInP4"
viewHelp "SurfacesInP4"

P4 = lines get "SurfacesInP4/P4Surfaces.txt";
P4_{0..10}

S = ZZ/31991[x,y,z,u,v]
pos = positions(P4,s -> match("--",s))
pos = drop(pos, 4)
#pos       
netList P4_pos
P4_9
betti res (I = first value P4_9)
J = saturate I
betti res J
degree J
