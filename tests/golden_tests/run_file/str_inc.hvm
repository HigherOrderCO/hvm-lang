(StrInc (len, buf)) = (len, #str λx (StrGo len #str (buf x)))

(StrGo 0 str) = str
(StrGo x (head, tail)) = ((+ 1 head), (StrGo (- x 1) tail))

// Old str encoding
Hello = (11, #str λx (104, (101, (108, (108, (111, (32, (119, (111, (114, (108, (100, x))))))))))))

main = (StrInc Hello)
