-- The following 3 lines have been placed (MES) into my init.m2 file
-*
prefix = "~/src/M2-eisenbud/M2/Macaulay2/packages/"
needsNewPackage = (name) -> needsPackage (name, FileName => prefix | name | ".m2")
installNewPackage = (name) -> installPackage (name, FileName => prefix | name | ".m2")
*-

----------------------------------------------------------
restart
uninstallPackage "FractionalIdeals"
uninstallPackage "NoetherNormalForm"
uninstallPackage "NoetherNormalization"
uninstallPackage "PushForward"

----------------------------------------------------------
restart
needsNewPackage "PushForward"
needsNewPackage "NoetherNormalization"
needsNewPackage "NoetherNormalForm"
needsNewPackage "FractionalIdeals"
peek loadedFiles

----------------------------------------------------------
restart
installNewPackage "PushForward"
installNewPackage "NoetherNormalization"
installNewPackage "NoetherNormalForm"
installNewPackage "FractionalIdeals"
----------------------------------------------------------
check "PushForward"
check "NoetherNormalization"
check "NoetherNormalForm" -- tests 0, 1, 3, 19, 21 fail (5 Aug 2021)
check "FractionalIdeals" -- tests 0 (5 Aug 2021)

----------------------------------------------------------
