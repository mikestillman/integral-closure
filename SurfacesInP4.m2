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

export {
    "readExampleFile",
    "getRing",
    "example",
    "names"
    }

readExampleFile = method()
--beginning of each example is ---*\\s
--ending of each is beginning of next
--each example is a string or collection of strings, looking like M2 code.
--allow several lines of comments (beginning with --)

readExampleFile String := HashTable => name -> (
    N := lines get name;
    re := "^---+ *(.*)"; -- at least -'s, followed by spaces, then grab the last match.
    pos := positions(N, s -> match(re,s));
    indices := for p in pos list (
            m := last regex(re, N#p);
            substring(m, N#p)
            );
    hashTable for i from 0 to #pos - 1 list indices#i => (
        p := pos#i;
        concatenate between("\n", if i == #pos - 1 then
            for j from p+1 to #N-1 list N#j
        else
            for j from p+1 to pos#(i+1)-1 list N#j
        ))
    )

getRing = () -> ZZ/31991[getSymbol "x", getSymbol "y", getSymbol "z", getSymbol "u", getSymbol "v"]
example = method()
example(String, HashTable) := (ind, exampleHash) -> (
    if not exampleHash#?ind then error "example does not exist";
    use getRing();
    value exampleHash#ind
    )

names = method()
names HashTable := (H) -> sort keys H

end--

regex("^---* *(.*)", "---   ab c d")
regex("^---* *(.*)", "---   --")

restart
needsPackage "SurfacesInP4"
P = readExampleFile "SurfacesInP4/P4Surfaces.txt";
names P

I = example("rat.d8.g6", P)
degree I
(genera I)#1 -- sectional genus
minimalBetti I

I = example("ab.d10.g6", P)

for k in keys P list (
    << "doing " << k << endl;
    I = example(k, P);
    time {k, degree I, genera I, minimalBetti I}
    )

I = example("enr.d11.g10", P) -- hmmm, not good
keys P
S = ZZ/31991[
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
positions(N, s -> 

s = "---     ab";

select
substring pos

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
J == I
