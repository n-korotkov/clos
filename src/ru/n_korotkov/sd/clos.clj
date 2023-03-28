(ns ru.n-korotkov.sd.clos
  "Common Lisp Object System for Clojure"
  (:refer-clojure :exclude [defmethod methods])
  (:use clojure.set))

(defn- map-nested
  ([f x]
    (map-nested f x []))
  ([f x ks]
    (if (map? x)
      (into (empty x) (map (fn [[k v]] [k (map-nested f v (conj ks k))]) x))
      (f ks x))))

(defn- dissoc-in [m ks]
  (case (count ks)
    0 m
    1 (dissoc m (peek ks))
    (update-in m (pop ks) #(dissoc % (peek ks)))))

(def ^:private hierarchy {})
(def ^:private class-desc {})
(def ^:private defined-classes {})
(def ^:private defined-generic-functions #{})
(def ^:private methods {:total 0})

(defn class-children    [class] (get-in hierarchy [class :children]))
(defn class-parents     [class] (get-in hierarchy [class :parents]))
(defn class-descendants [class] (reduce into #{class} (map class-descendants (class-children class))))
(defn class-ancestors   [class] (reduce into #{class} (map class-ancestors (class-parents class))))

(defn class-version     [class] (-> class class-desc count dec))

(defn- class-slot-map    [class] (-> class class-desc peek :slot-map))
(defn- class-depth       [class] (-> class class-desc peek :depth))
(defn- class-initargs    [class] (-> class class-desc peek :initargs))
(defn- class-initforms   [class] (-> class class-desc peek :initforms))
(defn- class-i-slots     [class] (-> class class-desc peek :i-slots))
(defn- class-c-slots     [class] (-> class class-desc peek :c-slots))

(def ^:private method-combinations
  {'+      (fn [args methods] (apply +      (map #(apply % [] args) methods)))
   'list   (fn [args methods] (apply list   (map #(apply % [] args) methods)))
   'concat (fn [args methods] (apply concat (map #(apply % [] args) methods)))
   'min    (fn [args methods] (apply min    (map #(apply % [] args) methods)))
   'max    (fn [args methods] (apply max    (map #(apply % [] args) methods)))
   'and    (fn [args methods] (reduce (fn [r m] (and r (apply m [] args))) true methods))
   'or     (fn [args methods] (reduce (fn [r m] (or  r (apply m [] args))) nil  methods))
   'do     (fn [args methods] (doseq [m methods] (apply m [] args)))})

(defn derived-from? [class ancestor]
  (and (not= class ancestor) (contains? (class-ancestors class) ancestor)))

(defn generic-fn? [x]
  (contains? defined-generic-functions (resolve x)))



(defn- populate-class-relations [class parents]
  (let [old-children (set (class-children class))
        add-child (fn [h parent] (update-in h [parent :children] #(conj % class)))
        update-parents #(reduce add-child % parents)]
    (alter-var-root #'hierarchy
      #(-> %
        (assoc-in [class :children] old-children)
        (assoc-in [class :parents] parents)
        (update-parents)))))

(defn- populate-class-desc [class parents slot-map]
  (let [old-c-slots (or (class-c-slots class) {})
        new-i-slots (->> slot-map
                      (filter (fn [[k v]] (not= (v :allocation) :class)))
                      (map first)
                      (into #{}))
        new-c-slots (->> slot-map
                      (filter (fn [[k v]] (= (v :allocation) :class)))
                      (map (fn [[k v]] [k (or (old-c-slots k) (volatile! (eval (v :initform))))]))
                      (into {}))
        new-initargs (->> slot-map
                       (map (fn [[k v]] [(v :initarg) k]))
                       (filter first)
                       (into {}))
        new-initforms (->> slot-map
                        (map (fn [[k v]] [k (v :initform)]))
                        (filter second)
                        (into {}))
        parent-i-slots (->> parents
                         (map class-i-slots)
                         (reduce into)
                         (remove #(contains? new-c-slots %))
                         (into #{}))
        parent-c-slots (->> parents
                         (map class-c-slots)
                         (reduce into)
                         (remove #(contains? new-i-slots (first %)))
                         (into {}))
        parent-initargs (reduce into {} (map class-initargs parents))
        parent-initforms (reduce into {} (map class-initforms parents))]
    (alter-var-root #'class-desc
      (fn [cd]
        (update cd class
          #(conj (vec %) {:slot-map  slot-map
                          :depth     (inc (apply max -1 (map class-depth parents)))
                          :i-slots   (into parent-i-slots new-i-slots)
                          :c-slots   (into parent-c-slots new-c-slots)
                          :initargs  (into parent-initargs new-initargs)
                          :initforms (into parent-initforms new-initforms)}))))))

(defn- populate-class-methods [class parents]
  (let [merge-methods (fn [x y] (merge-with #(merge-with into %1 %2) x y))]
    (alter-var-root #'methods
      (fn [m] (update m class #(apply merge-with merge-methods (into {} %) (map m parents)))))))

(defn- repopulate-class-relations [class parents]
  (let [remove-child (fn [h parent] (update-in h [parent :children] #(disj % class)))
        update-parents #(reduce remove-child % parents)]
    (alter-var-root #'hierarchy update-parents)
    (populate-class-relations class parents)))

(defn- repopulate-class-methods [class parents]
  (alter-var-root #'methods
    (fn [m]
      (assoc m class
        (map-nested
         (fn [[func i combination-type] signatures]
           (set (filter #(= (nth % i) class) signatures)))
         (m class)))))
  (populate-class-methods class parents))



(deftype T [])
(populate-class-relations T [])
(populate-class-desc T [] {})
(populate-class-methods T [])



(defn- add-class [class parents slot-map]
  (populate-class-relations class parents)
  (populate-class-desc class parents slot-map)
  (populate-class-methods class parents))

(defn- update-class [class parents slot-map]
  (repopulate-class-relations class parents)
  (populate-class-desc class parents slot-map)
  (repopulate-class-methods class parents))

(defn defclass- [name qname base-classes slot-map]
  (let [redefinition? (contains? defined-classes qname)
        keep-parents (fn [ps] (filterv (fn [c] (not-any? #(derived-from? % c) ps)) ps))]
    (when-not redefinition?
      (alter-var-root #'defined-classes #(assoc % qname (eval `(deftype ~name [~'iSlots ~'cSlots ~'classVersion])))))
    (let [parents (keep-parents (or (not-empty base-classes) [T]))
          class (resolve qname)]
      (if redefinition?
        (let [descendants (sort-by (comp - class-depth) (disj (class-descendants class) class))
              old-slot-map (class-slot-map class)
              slot-accessors (remove nil? (mapcat (fn [[_ v]] [(v :reader) (v :writer)]) old-slot-map))
              remove-slot-accessor (fn [func class]
                                     (doseq [d-class (class-descendants class)]
                                       (alter-var-root #'methods (fn [m] (update-in m [d-class func 0 :primary] #(disj % [class])))))
                                     (alter-var-root #'methods #(dissoc-in % [func :primary class])))]
          (doseq [slot-accessor slot-accessors]
            (remove-slot-accessor (resolve slot-accessor) class))
          (update-class class parents slot-map)
          (doseq [d-class descendants]
            (update-class d-class (keep-parents (class-parents d-class)) (class-slot-map d-class))))
        (add-class class parents slot-map)))))

(defmacro defclass [name base-classes slot-definitions]
  (let [qname (symbol (str (namespace-munge *ns*) "." name))
        destructure-slot #(if (seq? %) [(first %) (apply hash-map (rest %))] [% {}])
        slot-map (into {} (map destructure-slot slot-definitions))
        readers (filter first (map (fn [[k v]] [(v :reader) k]) slot-map))
        writers (filter first (map (fn [[k v]] [(v :writer) k]) slot-map))
        define-readers (map
                        (fn [[k v]]
                          `(defmethod ~k [(obj# ~name)]
                            (update-obsolete-instance obj#)
                            (if (.containsKey (.cSlots obj#) '~v)
                              @(.get (.cSlots obj#) '~v)
                              (.get (.iSlots obj#) '~v))))
                        readers)
        define-writers (map
                        (fn [[k v]]
                          `(defmethod ~k [(obj# ~name) val#]
                            (update-obsolete-instance obj#)
                            (if (.containsKey (.cSlots obj#) '~v)
                              (vreset! (.get (.cSlots obj#) '~v) val#)
                              (.put (.iSlots obj#) '~v val#))))
                        writers)]
    `(do
      (defclass- '~name '~qname (map resolve '~base-classes) '~slot-map)
      ~@define-readers
      ~@define-writers)))

(defn make-instance- [class-name arg-map]
  (let [class (resolve class-name)
        obj (eval `(new ~class
                    (java.util.HashMap.)
                    (java.util.HashMap.)
                    (java.util.concurrent.atomic.AtomicInteger. (class-version ~class))))]
    (doseq [[initarg val] arg-map]
      (let [slot-name ((class-initargs class) initarg)]
        (if (contains? (class-c-slots class) slot-name)
          (vreset! ((class-c-slots class) slot-name) val)
          (.put (.iSlots obj) slot-name val))))
    (doseq [[slot-name vol] (class-c-slots class)]
      (.put (.cSlots obj) slot-name vol))
    (doseq [slot-name (class-i-slots class)]
      (when-not (.containsKey (.iSlots obj) slot-name)
        (.put (.iSlots obj) slot-name (eval ((class-initforms class) slot-name)))))
    obj))

(defmacro make-instance [class-name & {:as arg-map}]
  `(make-instance- '~class-name ~arg-map))



(defn- run-without-combination [args primary before after around]
  (let [after-around (fn [next-methods & s]
                       (let [_ (doseq [method before] (apply method [] s))
                             r (when-not (empty? primary) (apply (first primary) (rest primary) s))
                             _ (doseq [method after] (apply method [] s))]
                         r))]
    (if (empty? around)
      (apply after-around [] args)
      (apply (first around) (rest (conj around after-around)) args))))

(defn- run-with-combination [args primary around comb-fn order]
  (let [primary-ordered (if (= order :most-specific-last) (reverse primary) primary)
        methods-combined (fn [next-methods & s] (comb-fn s primary-ordered))]
    (if (empty? around)
      (apply methods-combined [] args)
      (apply (first around) (rest (conj around methods-combined)) args))))

(defn remove-generic-fn [func]
  (doseq [[_ methods-of-type] (methods func)
          [signature _] methods-of-type
          arg-class signature
          d-class (class-descendants arg-class)]
    (alter-var-root #'methods #(dissoc-in % [d-class func])))
  (alter-var-root #'methods #(dissoc % func)))

(defn run-generic-fn [func args comb order]
  (let [cmp #(compare
              (conj (mapv class-depth %2) ((meta %2) :ord))
              (conj (mapv class-depth %1) ((meta %1) :ord)))
        comb-fn (method-combinations comb)
        arg-classes (map class args)
        method-signatures (reduce #(merge-with intersection %1 %2) (map #(get-in methods [%1 func %2]) arg-classes (iterate inc 0)))
        get-methods-by-type (fn [type] (mapv #(get-in methods [func type %]) (sort cmp (method-signatures type))))
        primary-methods (get-methods-by-type :primary)
        before-methods (get-methods-by-type :before)
        after-methods (reverse (get-methods-by-type :after))
        around-methods (get-methods-by-type :around)]
    (if (nil? comb-fn)
      (run-without-combination args primary-methods before-methods after-methods around-methods)
      (run-with-combination args primary-methods around-methods comb-fn order))))

(defmacro defgeneric [name args & {comb :method-combination, order :order, :or {order :most-specific-first}}]
  `(do
    (def ~name)
    (remove-generic-fn ~name)
    (intern *ns* '~name (fn ~args (run-generic-fn ~name ~args '~comb ~order)))
    (alter-var-root #'defined-generic-functions #(conj % #'~name))))


(defn defmethod- [func method-type method arg-classes]
  (let [arg-classes (with-meta (map #(or % T) arg-classes) {:ord (methods :total)})
        classes-enum (map vector (iterate inc 0) arg-classes)]
    (when-not (contains? (get-in methods [func method-type]) arg-classes)
      (doseq [[i exact-class] classes-enum
              class (class-descendants exact-class)]
        (alter-var-root #'methods
          (fn [m] (update-in m [class func i method-type] #(conj (set %) arg-classes))))))
    (alter-var-root #'methods
      #(-> %
        (assoc-in [func method-type arg-classes] method)
        (update :total inc)))))

(defmacro defmethod [name & args]
  (let [arg-head (first args)
        qualifier (when (contains? #{:before :after :around} arg-head) arg-head)
        [func-args & body] (if qualifier (rest args) args)
        arg-class-names (mapv #(if (seq? %) (second %) 'ru.n_korotkov.sd.clos.T) func-args)
        arg-names (mapv #(if (seq? %) (first %) %) func-args)]
    `(do
      ~(when (simple-symbol? name)
        `(when (not (generic-fn? '~name)) (defgeneric ~name ~arg-names)))
      (defmethod-
        ~name
        (or ~qualifier :primary)
        (fn [next-methods# ~@arg-names]
          (let [~'call-next-method (fn cnm#
                                     ([] (cnm# ~@arg-names))
                                     ([& args#] (apply (first next-methods#) (rest next-methods#) args#)))]
            ~@body))
        (map resolve '~arg-class-names)))))



(defmethod update-instance-for-redefined-class
  [obj added-slots removed-slots removed-slot-map initforms]
  (doseq [slot-name added-slots]
    (when-not (.containsKey (.iSlots obj) slot-name)
      (.put (.iSlots obj) slot-name (eval (initforms slot-name))))))

(defn update-obsolete-instance [obj]
  (doseq [new-version (subvec (class-desc (class obj)) (inc (.classVersion obj)))]
    (let [old-version (nth (class-desc (class obj)) (.classVersion obj))
          old-i-slots (set (old-version :i-slots))
          new-i-slots (set (new-version :i-slots))
          old-c-slots (set (keys (old-version :c-slots)))
          new-c-slots (set (keys (new-version :c-slots)))
          c->i-slots (intersection old-c-slots new-i-slots)
          removed-i-slots (difference old-i-slots new-i-slots)
          removed-c-slots (difference old-c-slots new-c-slots)
          added-i-slots (difference new-i-slots old-i-slots c->i-slots)
          added-c-slots (difference new-c-slots old-c-slots)
          removed-slot-map (->> removed-i-slots
                             (filter #(.containsKey (.iSlots obj) %))
                             (map (fn [slot-name] [slot-name (.get (.iSlots obj) slot-name)]))
                             (into {}))]
      (doseq [removed-i-slot removed-i-slots] (.remove (.iSlots obj) removed-i-slot))
      (doseq [removed-c-slot removed-c-slots] (.remove (.cSlots obj) removed-c-slot))
      (doseq [c->i-slot c->i-slots] (.put (.iSlots obj) c->i-slot @((old-version :c-slots) c->i-slot)))
      (doseq [added-c-slot added-c-slots] (.put (.cSlots obj) added-c-slot ((new-version :c-slots) added-c-slot)))
      (update-instance-for-redefined-class obj added-i-slots removed-i-slots removed-slot-map (new-version :initforms))
      (.getAndIncrement (.classVersion obj)))))
