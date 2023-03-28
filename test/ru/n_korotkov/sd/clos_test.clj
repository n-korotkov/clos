(ns ru.n-korotkov.sd.clos-test
  (:require
   [ru.n-korotkov.sd.clos :as clos]
   [clojure.test :as test]))

(defn approx= [x y]
  (< (Math/abs (- x y)) 1e-12))

(clos/defclass Root []
  [(a :initarg :a :initform "A" :reader get-a :writer set-a)])

(clos/defclass Base- [Root]
  [(b :initarg :b :initform "B" :reader get-b :writer set-b :allocation :instance)
   (c :initarg :c :initform "C" :reader get-c :writer set-c)
   (x :initarg :x :initform "X" :reader get-x :writer set-x :allocation :class)
   (y :initarg :y :initform "Y" :reader get-y :writer set-y :allocation :class)])

(clos/defclass Base+ [Root]
  [(b :initarg :b :initform "BB" :reader get-b :writer set-b)
   (d :initarg :d :initform "DD" :reader get-d :writer set-d :allocation instance)
   (x :initarg :x :initform "XX" :reader get-x :writer set-x :allocation :class)
   (z :initarg :z :initform "ZZ" :reader get-z :writer set-z :allocation :class)])

(clos/defclass Derived [Base+ Base-] [])

(clos/defclass Derived* [Base- Base+]
  [(b :initarg :b* :initform "B*" :reader get-b* :writer set-b* :allocation :instance)
   (x :initarg :x* :initform "X*" :reader get-x* :writer set-x* :allocation :class)])

(clos/defclass Derived- [Base- Base+]
  [(c :initarg :c- :initform "C-" :reader get-c- :writer set-c- :allocation :instance)
   (y :initarg :y- :initform "Y-" :reader get-y- :writer set-y- :allocation :class)])

(clos/defclass Derived+ [Base+ Base-]
  [(d :initarg :d+ :initform "D+" :reader get-d+ :writer set-d+ :allocation :class)
   (z :initarg :z+ :initform "Z+" :reader get-z+ :writer set-z+ :allocation :instance)])

(test/deftest slot-inheritance-test
  (let [root (clos/make-instance Root)
        base- (clos/make-instance Base-)
        derived (clos/make-instance Derived :a "a" :y "y")
        derived+1 (clos/make-instance Derived+)
        derived+2 (clos/make-instance Derived+ :d+ "d" :z+ "z")]
    (test/testing "Local slots"
      (test/is (= (get-a base-) "A"))
      (test/are [reader value] (= (reader derived) value)
        get-a "a"
        get-b "B"
        get-c "C"
        get-d "DD"))
    (test/testing "Shared slots"
      (test/are [reader value] (= (reader derived) value)
        get-x "X"
        get-y "y"
        get-z "ZZ"))
    (test/testing "Local to shared"
      (test/are [obj value] (= (get-d+ obj) value)
        derived+1 "d"
        derived+2 "d"))
    (test/testing "Shared to local"
      (test/are [obj value] (= (get-z+ obj) value)
        derived+1 "Z+"
        derived+2 "z"))))


(clos/defclass X []  [(x :reader get-x :writer set-x :initform "")])
(clos/defclass A [X] [])      ;      X      0
(clos/defclass B [X] [])      ;     /|      
(clos/defclass C [B] [])      ;    A B      1
(clos/defclass D [B] [])      ;    | |\     
(clos/defclass E [A C] [])    ;    | C D    2
(clos/defclass F [C] [])      ;    |/| |    
(clos/defclass G [D] [])      ;    E F G    3
(clos/defclass H [E F] [])    ;     \|      
(clos/defclass I [H] [])      ;      H      4
(clos/defclass J [I] [])      ;      |      
(clos/defclass K [I] [])      ;      I      5
(clos/defclass L [I] [])      ;     /|\     
(clos/defclass M [J] [])      ;    J K L    6
(clos/defclass N [J] [])      ;   /| | |\   
(clos/defclass O [K] [])      ;  M N O | P  7
(clos/defclass P [L] [])      ;   \ \|\| |  
(clos/defclass Q [N O] [])    ;    \ Q R S  8
(clos/defclass R [O L] [])    ;     \|/ \|  
(clos/defclass S [P] [])      ;      T   U  9
(clos/defclass T [M Q R] [])  ;          |  
(clos/defclass U [R S] [])    ;          V  10
(clos/defclass V [U] [])

(clos/defmethod update-x [(a X) f]
  (set-x a (f (get-x a))))


(test/deftest method-order-test
  (clos/defmethod ord-f [a] "")
  (clos/defmethod ord-f [(a M)] (str "M" (call-next-method)))
  (clos/defmethod ord-f [(a R)] (str "R" (call-next-method)))
  (clos/defmethod ord-f [(a O)] (str "O" (call-next-method)))
  (clos/defmethod ord-f [(a Q)] (str "Q" (call-next-method)))
  (clos/defmethod ord-f [(a N)] (str "N" (call-next-method)))
  (test/is (= (ord-f (clos/make-instance T)) "QRNOM")))


(test/deftest multimethod-test
  (clos/defmethod aux-f [a b] "|")
  (clos/defmethod aux-f [(a A) (b B)] (str "AB-" (call-next-method)))
  (clos/defmethod aux-f [(a T) (b T)] (str "TT-" (call-next-method)))
  (clos/defmethod aux-f [(a J) (b R)] (str "JR-" (call-next-method)))
  (clos/defmethod aux-f [(a M) (b L)] (str "ML-" (call-next-method)))
  (clos/defmethod aux-f [(a E) (b G)] (str "EG-" (call-next-method)))
  (clos/defmethod aux-f [(a I) (b N)] (str "IN-" (call-next-method)))
  (clos/defmethod aux-f :before [(a E) (b B)] (update-x a #(str % "EB>")))
  (clos/defmethod aux-f :before [(a Q) (b P)] (update-x a #(str % "QP>")))
  (clos/defmethod aux-f :after  [(a E) (b B)] (update-x a #(str % "EB<")))
  (clos/defmethod aux-f :after  [(a Q) (b P)] (update-x a #(str % "QP<")))
  (clos/defmethod aux-f :around [(a E) (b B)] (str "EB=" (call-next-method)))
  (clos/defmethod aux-f :around [(a Q) (b P)] (str "QP=" (call-next-method)))
  (let [t (clos/make-instance T)
        u (clos/make-instance U)]
    (test/testing "Primary methods"
      (test/is (= (aux-f t u) "QP=EB=ML-JR-AB-|"))
      (test/is (= (aux-f u t) "EB=IN-AB-|")))
    (test/testing "Auxiliary methods"
      (test/is (= (get-x t) "QP>EB>EB<QP<"))
      (test/is (= (get-x u) "EB>EB<")))))


(test/deftest method-combination-test
  (clos/defgeneric comb-f [a] :method-combination concat :order :most-specific-last)
  (clos/defmethod comb-f [a]     [1])
  (clos/defmethod comb-f [(a C)] [2])
  (clos/defmethod comb-f [(a M)] [3])
  (clos/defmethod comb-f [(a L)] [4])
  (let [q (clos/make-instance Q)
        m (clos/make-instance M)
        u (clos/make-instance U)
        t (clos/make-instance T)]
    (test/are [obj value] (= (comb-f obj) value)
      q '(1 2)
      m '(1 2 3)
      u '(1 2 4)
      t '(1 2 4 3))))


(test/deftest class-redefinition-test
  (clos/defclass Point []
    [(x :reader get-x :initarg :x :initform 0.0)
     (y :reader get-y :initarg :y :initform 0.0)])

  (def position (clos/make-instance Point :x 1.0 :y 1.0))

  (clos/defclass Point []
    [(rho :reader get-rho :initarg :rho :initform 0.0)
     (theta :reader get-theta :initarg :theta :initform 0.0)])

  (clos/defmethod clos/update-instance-for-redefined-class :before
    [(pos Point) added removed slot-map initforms]
    (let [x (slot-map 'x)
          y (slot-map 'y)]
      (.put (.iSlots pos) 'rho (Math/sqrt (+ (* x x) (* y y))))
      (.put (.iSlots pos) 'theta (Math/atan2 y x))))

  (clos/defmethod get-x [(pos Point)]
    (let [rho (get-rho pos)
          theta (get-theta pos)]
      (* rho (Math/cos theta))))

  (clos/defmethod get-y [(pos Point)]
    (let [rho (get-rho pos)
          theta (get-theta pos)]
      (* rho (Math/sin theta))))

  (test/is (approx= (get-x position) 1.0))
  (test/is (approx= (get-y position) 1.0))
  (test/is (approx= (get-rho position) (Math/sqrt 2)))
  (test/is (approx= (get-theta position) (/ (Math/PI) 4))))

(test/run-tests)
