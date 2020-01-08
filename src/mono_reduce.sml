(* Copyright (c) 2008, 2013-2014, Adam Chlipala
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 *   this list of conditions and the following disclaimer.
 * - Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * - The names of contributors may not be used to endorse or promote products
 *   derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR 
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *)

(* Simplify a Mono program algebraically *)

structure MonoReduce :> MONO_REDUCE = struct

open Mono

val fullMode = ref false

structure E = MonoEnv
structure U = MonoUtil

structure IM = IntBinaryMap
structure IS = IntBinarySet

structure SS = BinarySetFn(struct
                            type ord_key = string
                            val compare = String.compare
                            end)

structure SLS = BinarySetFn(struct
                             type ord_key = string list
                             val compare = Order.joinL String.compare
                             end)

val cachedVals = ref ([]: ({ name: string
                           , fullname: string
                           , seqNum: int
                           , typ: typ
                           , orig: exp
                           , optim: exp
                           } list))
val cachedValRecs = ref ([]: (({ name: string
                               , fullname: string
                               , seqNum: int
                               , typ: typ
                               , orig: exp
                               , optim: exp
                               } list) list))
val cachedDatatypes = ref ([]: (({ name: string
                                 , seqNum: int
                                 , constructors: (string * int * typ option) list} list ) list))

type mapping = { named: IS.set IM.map
               , constructors: IS.set IM.map
               , datatypes: IS.set IM.map
               }  

fun simpleTypeImpure tsyms =
    U.Typ.exists (fn TFun _ => true
                   | TDatatype (n, _) => IS.member (tsyms, n)
                   | _ => false)

fun simpleImpure isGlobal (tsyms, syms) =
    U.Exp.existsB {typ = fn _ => false,
                   exp = fn (env, e) =>
                            case e of
                                EWrite _ => true
                              | EQuery _ => true
                              | EDml _ => true
                              | ENextval _ => true
                              | ESetval _ => true
                              | EFfiApp (m, x, _) => Settings.isEffectful (m, x) orelse Settings.isBenignEffectful (m, x)
                              | EServerCall _ => true
                              | ERecv _ => true
                              | ESleep _ => true
                              | ENamed n => IS.member (syms, n)
                              | ERel n =>
                                let
                                    val (_, t, _) = E.lookupERel env n
                                in
                                    simpleTypeImpure tsyms t
                                end
                              | EApp _ => not isGlobal
                              | _ => false,
                   bind = fn (env, b) =>
                             case b of
                                 U.Exp.RelE (x, t) => E.pushERel env x t NONE
                               | _ => env}

fun impure (e, _) =
    case e of
        EWrite _ => true
      | EQuery _ => true
      | EDml _ => true
      | ENextval _ => true
      | ESetval _ => true
      | EUnurlify (e, _, _) => impure e
      | EAbs _ => false

      | EPrim _ => false
      | ERel _ => false
      | ENamed _ => false
      | ECon (_, _, eo) => (case eo of NONE => false | SOME e => impure e)
      | ENone _ => false
      | ESome (_, e) => impure e
      | EFfi _ => false
      | EFfiApp (m, x, _) => Settings.isEffectful (m, x) orelse Settings.isBenignEffectful (m, x)
      | EApp ((EFfi _, _), _) => false
      | EApp _ => true

      | EUnop (_, e) => impure e
      | EBinop (_, _, e1, e2) => impure e1 orelse impure e2

      | ERecord xes => List.exists (fn (_, e, _) => impure e) xes
      | EField (e, _) => impure e

      | ECase (e, pes, _) => impure e orelse List.exists (fn (_, e) => impure e) pes

      | EError _ => true
      | EReturnBlob {blob = NONE, mimeType = e2, ...} => impure e2
      | EReturnBlob {blob = SOME e1, mimeType = e2, ...} => impure e1 orelse impure e2
      | ERedirect (e, _) => impure e

      | EStrcat (e1, e2) => impure e1 orelse impure e2

      | ESeq (e1, e2) => impure e1 orelse impure e2
      | ELet (_, _, e1, e2) => impure e1 orelse impure e2

      | EClosure (_, es) => List.exists impure es
      | EJavaScript (_, e) => impure e
      | ESignalReturn e => impure e
      | ESignalBind (e1, e2) => impure e1 orelse impure e2
      | ESignalSource e => impure e
      | EServerCall _ => true
      | ERecv _ => true
      | ESleep _ => true
      | ESpawn _ => true

val liftExpInExp = Monoize.liftExpInExp

fun multiLift n e =
    case n of
        0 => e
      | _ => multiLift (n - 1) (liftExpInExp 0 e)

val subExpInExp' =
    U.Exp.mapB {typ = fn t => t,
                exp = fn (xn, rep) => fn e =>
                                  case e of
                                      ERel xn' =>
                                      (case Int.compare (xn', xn) of
                                           EQUAL => #1 rep
                                         | GREATER=> ERel (xn' - 1)
                                         | LESS => e)
                                    | _ => e,
                bind = fn ((xn, rep), U.Exp.RelE _) => (xn+1, liftExpInExp 0 rep)
                        | (ctx, _) => ctx}

fun subExpInExp (n, e1) e2 =
    let
        val r = subExpInExp' (n, e1) e2
    in
        (*Print.prefaces "subExpInExp" [("e1", MonoPrint.p_exp MonoEnv.empty e1),
                                      ("e2", MonoPrint.p_exp MonoEnv.empty e2),
                                      ("r", MonoPrint.p_exp MonoEnv.empty r)];*)
        r
    end

fun typ c = c

val swapExpVars =
    U.Exp.mapB {typ = fn t => t,
                exp = fn lower => fn e =>
                                     case e of
                                         ERel xn =>
                                         if xn = lower then
                                             ERel (lower + 1)
                                         else if xn = lower + 1 then
                                             ERel lower
                                         else
                                             e
                                       | _ => e,
                bind = fn (lower, U.Exp.RelE _) => lower+1
                        | (lower, _) => lower}

val swapExpVarsPat =
    U.Exp.mapB {typ = fn t => t,
                exp = fn (lower, len) => fn e =>
                                     case e of
                                         ERel xn =>
                                         if xn = lower then
                                             ERel (lower + len)
                                         else if xn >= lower + 1 andalso xn < lower + 1 + len then
                                             ERel (xn - 1)
                                         else
                                             e
                                       | _ => e,
                bind = fn ((lower, len), U.Exp.RelE _) => (lower+1, len)
                        | (st, _) => st}

datatype result = Yes of (string * typ * exp) list | No | Maybe

fun match (env, p : pat, e : exp) =
    case (#1 p, #1 e) of
        (PVar (x, t), _) => Yes ((x, t, e) :: env)

      | (PPrim (Prim.String (_, s)), EStrcat ((EPrim (Prim.String (_, s')), _), _)) =>
        if String.isPrefix s' s then
            Maybe
        else
            No

      | (PPrim (Prim.String (_, s)), EStrcat (_, (EPrim (Prim.String (_, s')), _))) =>
        if String.isSuffix s' s then
            Maybe
        else
            No

      | (PPrim p, EPrim p') =>
        if Prim.equal (p, p') then
            Yes env
        else
            No

      | (PPrim (Prim.String (_, s)), _) =>
        let
            fun lengthLb (e : exp) =
                case #1 e of
                    EStrcat (e1, e2) => lengthLb e1 + lengthLb e2
                  | EPrim (Prim.String (_, s)) => size s
                  | _ => 0
        in
            if lengthLb e > size s then
                No
            else
                Maybe
        end

      | (PCon (_, PConVar n1, po), ECon (_, PConVar n2, eo)) =>
        if n1 = n2 then
            case (po, eo) of
                (NONE, NONE) => Yes env
              | (SOME p, SOME e) => match (env, p, e)
              | _ => Maybe
        else
            No

      | (PCon (_, PConFfi {mod = m1, con = con1, ...}, NONE), ECon (_, PConFfi {mod = m2, con = con2, ...}, NONE)) =>
        if m1 = m2 andalso con1 = con2 then
            Yes env
        else
            No

      | (PCon (_, PConFfi {mod = m1, con = con1, ...}, SOME ep), ECon (_, PConFfi {mod = m2, con = con2, ...}, SOME e)) =>
        if m1 = m2 andalso con1 = con2 then
            match (env, p, e)
        else
            No

      | (PRecord xps, ERecord xes) =>
        let
            fun consider (xps, env) =
                case xps of
                    [] => Yes env
                  | (x, p, _) :: rest =>
                    case List.find (fn (x', _, _) => x' = x) xes of
                        NONE => No
                      | SOME (_, e, _) =>
                        case match (env, p, e) of
                            No => No
                          | Maybe => Maybe
                          | Yes env => consider (rest, env)
        in
            consider (xps, env)
        end

      | (PNone _, ENone _) => Yes env
      | (PNone _, ESome _) => No
      | (PSome (_, p), ESome (_, e)) => match (env, p, e)
      | (PSome _, ENone _) => No

      | _ => Maybe

datatype event =
         WritePage
       | ReadDb
       | WriteDb
       | ReadCookie
       | WriteCookie
       | UseRel
       | Unsure
       | Abort

fun p_event e =
    let
        open Print.PD
    in
        case e of
            WritePage => string "WritePage"
          | ReadDb => string "ReadDb"
          | WriteDb => string "WriteDb"
          | ReadCookie => string "ReadCookie"
          | WriteCookie => string "WriteCookie"
          | UseRel => string "UseRel"
          | Unsure => string "Unsure"
          | Abort => string "Abort"
    end

val p_events = Print.p_list p_event

fun patBinds (p, _) =
    case p of
        PVar _ => 1
      | PPrim _ => 0
      | PCon (_, _, NONE) => 0
      | PCon (_, _, SOME p) => patBinds p
      | PRecord xpts => foldl (fn ((_, p, _), n) => n + patBinds p) 0 xpts
      | PNone _ => 0
      | PSome (_, p) => patBinds p

val countFree = U.Exp.foldB {typ = fn (_, n) => n,
                             exp = fn (x, e, n) =>
                                      case e of
                                          ERel x' => if x = x' then n + 1 else n
                                        | _ => n,
                             bind = fn (n, b) =>
                                       case b of
                                           U.Exp.RelE _ => n + 1
                                     | _ => n}

val freeInAbs = U.Exp.existsB {typ = fn _ => false,
                               exp = fn (n, e) =>
                                        case e of
                                            EAbs (_, _, _, b) => countFree n 0 b > 0
                                          | EJavaScript (_, b) => countFree n 0 b > 0
                                          | _ => false,
                               bind = fn (n, b) =>
                                         case b of
                                             U.Exp.RelE _ => n + 1
                                           | _ => n} 0

val yankedCase = ref false

fun reduce' (file : file) =
    let
        val (timpures, impures, absCounts) =
            foldl (fn ((d, _), (timpures, impures, absCounts)) =>
                      let
                          fun countAbs env e =
                              case #1 e of
                                  EAbs (x, t, _, e) => 1 + countAbs (E.pushERel env x t NONE) e
                                | _ =>
                                  let
                                      fun remaining e =
                                          case #1 e of
                                              ENamed n => IM.find (absCounts, n)
                                            | EApp (e, arg) =>
                                              if simpleImpure true (timpures, impures) env arg then
                                                  NONE
                                              else
                                                  (case remaining e of
                                                       NONE => NONE
                                                     | SOME n => if n > 0 then
                                                                     SOME (n - 1)
                                                                 else
                                                                     NONE)
                                            | _ => NONE
                                  in
                                      getOpt (remaining e, 0)
                                  end
                      in
                          case d of
                              DDatatype dts =>
                              (if List.exists (fn (_, _, cs) =>
                                                  List.exists (fn (_, _, NONE) => false
                                                                | (_, _, SOME t) => simpleTypeImpure timpures t) cs)
                                              dts then
                                   IS.addList (timpures, map #2 dts)
                               else
                                   timpures,
                               impures,
                               absCounts)
                            | DVal (_, n, _, e, _) =>
                              (timpures,
                               if simpleImpure true (timpures, impures) E.empty e then
                                   IS.add (impures, n)
                               else
                                   impures,
                               IM.insert (absCounts, n, countAbs E.empty e))
                            | DValRec vis =>
                              (timpures,
                               if List.exists (fn (_, _, _, e, _) => simpleImpure true (timpures, impures) E.empty e) vis then
                                   foldl (fn ((_, n, _, _, _), impures) =>
                                             IS.add (impures, n)) impures vis
                               else
                                   impures,
                               foldl (fn ((x, n, _, e, _), absCounts) =>
                                         IM.insert (absCounts, n, countAbs E.empty e))
                                     absCounts vis)
                            | _ => (timpures, impures, absCounts)
                      end)
                  (IS.empty, IS.empty, IM.empty) (#1 file)

        val uses = U.File.fold {typ = fn (_, m) => m,
                                exp = fn (e, m) =>
                                         case e of
                                             ENamed n => IM.insert (m, n, 1 + Option.getOpt (IM.find (m, n), 0))
                                           | _ => m,
                                decl = fn (_, m) => m}
                               IM.empty file

        val size = U.Exp.fold {typ = fn (_, n) => n,
                               exp = fn (_, n) => n + 1} 0

        val functionInside' = U.Typ.exists (fn c => case c of
                                                        TFun _ => true
                                                      | _ => false)
                              
        fun functionInside t =
            case #1 t of
                TFun (t1, t2) => functionInside' t1 orelse functionInside t2
              | _ => functionInside' t

        fun mayInline (n, e, t, s) =
            case IM.find (uses, n) of
                NONE => false
              | SOME count => not (Settings.checkNeverInline s)
                              andalso (count <= 1
                                       orelse size e <= Settings.getMonoInline ()
                                       orelse functionInside t
                                       orelse Settings.checkAlwaysInline s)

        fun summarize d (e, _) =
            let
                val s =
                    case e of
                        EPrim _ => []
                      | ERel n => if n = d then [UseRel] else []
                      | ENamed _ => []
                      | ECon (_, _, NONE) => []
                      | ECon (_, _, SOME e) => summarize d e
                      | ENone _ => []
                      | ESome (_, e) => summarize d e
                      | EFfi _ => []
                      | EFfiApp ("Basis", "get_cookie", [(e, _)]) =>
                        summarize d e @ [ReadCookie]
                      | EFfiApp ("Basis", "set_cookie", es) =>
                        List.concat (map (summarize d o #1) es) @ [WriteCookie]
                      | EFfiApp ("Basis", "clear_cookie", es) =>
                        List.concat (map (summarize d o #1) es) @ [WriteCookie]
                      | EFfiApp (m, x, es) =>
                        if Settings.isEffectful (m, x) orelse Settings.isBenignEffectful (m, x) then
                            List.concat (map (summarize d o #1) es) @ [if m = "Basis" andalso String.isSuffix "_w" x then
                                                                           WritePage
                                                                       else
                                                                           Unsure]
                        else
                            List.concat (map (summarize d o #1) es)
                      | EApp ((EFfi _, _), e) => summarize d e
                      | EApp _ =>
                        let
                            fun unravel (e, passed, ls) =
                                case e of
                                    ENamed n =>
                                    let
                                        val ls = rev ls
                                    in
                                        if IS.member (impures, n) then
                                            case IM.find (absCounts, n) of
                                                NONE => [Unsure]
                                              | SOME len =>
                                                if passed < len then
                                                    ls
                                                else
                                                    ls @ [Unsure]
                                        else
                                            ls
                                    end
                                  | ERel n => List.revAppend (ls,
                                                              if n = d then
                                                                  [UseRel, Unsure]
                                                              else
                                                                  [Unsure])
                                  | EApp (f, x) =>
                                    unravel (#1 f, passed + 1, List.revAppend (summarize d x,
                                                                               ls))
                                  | EError _ => [Abort]
                                  | _ => [Unsure]
                        in
                            unravel (e, 0, [])
                        end

                      | EAbs _ => []

                      | EUnop (_, e) => summarize d e
                      | EBinop (_, _, e1, e2) => summarize d e1 @ summarize d e2

                      | ERecord xets => List.concat (map (summarize d o #2) xets)
                      | EField (e, _) => summarize d e

                      | ECase (e, pes, _) =>
                        let
                            val lss = map (fn (p, e) => summarize (if d = ~1 then ~1 else d + patBinds p) e) pes

                            fun splitRel ls acc =
                                case ls of
                                    [] => (acc, false, ls)
                                  | UseRel :: ls  => (acc, true, ls)
                                  | v :: ls => splitRel ls (v :: acc)

                            val (pre, used, post) = foldl (fn (ls, (pre, used, post)) =>
                                                              let
                                                                  val (pre', used', post') = splitRel ls []
                                                              in
                                                                  (pre' @ pre, used' orelse used, post' @ post)
                                                              end)
                                                    ([], false, []) lss
                        in
                            summarize d e
                            @ pre
                            @ (if used then [UseRel] else [])
                            @ post
                        end
                      | EStrcat (e1, e2) => summarize d e1 @ summarize d e2

                      | EError (e, _) => summarize d e @ [Abort]
                      | EReturnBlob {blob = NONE, mimeType = e2, ...} => summarize d e2 @ [Abort]
                      | EReturnBlob {blob = SOME e1, mimeType = e2, ...} => summarize d e1 @ summarize d e2 @ [Abort]
                      | ERedirect (e, _) => summarize d e @ [Abort]

                      | EWrite e => summarize d e @ [WritePage]
                                    
                      | ESeq (e1, e2) => summarize d e1 @ summarize d e2
                      | ELet (_, _, e1, e2) => summarize d e1 @ summarize (if d = ~1 then ~1 else d + 1) e2

                      | EClosure (_, es) => List.concat (map (summarize d) es)

                      | EQuery {query, body, initial, ...} =>
                        List.concat [summarize d query,
                                     summarize d initial,
                                     [ReadDb],
                                     summarize (if d = ~1 then ~1 else d + 2) body]

                      | EDml (e, _) => summarize d e @ [WriteDb]
                      | ENextval e => summarize d e @ [WriteDb]
                      | ESetval (e1, e2) => summarize d e1 @ summarize d e2 @ [WriteDb]
                      | EUnurlify (e, _, _) => summarize d e
                      | EJavaScript (_, e) => summarize d e
                      | ESignalReturn e => summarize d e
                      | ESignalBind (e1, e2) => summarize d e1 @ summarize d e2
                      | ESignalSource e => summarize d e

                      | EServerCall (e, _, _, _) => summarize d e @ [Unsure]
                      | ERecv (e, _) => summarize d e @ [Unsure]
                      | ESleep e => summarize d e @ [Unsure]
                      | ESpawn e => summarize d e @ [Unsure]
            in
                (*Print.prefaces "Summarize"
                               [("e", MonoPrint.p_exp MonoEnv.empty (e, ErrorMsg.dummySpan)),
                                ("d", Print.PD.string (Int.toString d)),
                                ("s", p_events s)];*)
                s
            end

        val impure = fn env => fn e =>
                        simpleImpure false (timpures, impures) env e andalso impure e
                        andalso not (List.null (summarize ~1 e))

        fun passive (e : exp) =
            case #1 e of
                EPrim _ => true
              | ERel _ => true
              | ENamed _ => true
              | ECon (_, _, NONE) => true
              | ECon (_, _, SOME e) => passive e
              | ENone _ => true
              | ESome (_, e) => passive e
              | EFfi _ => true
              | EAbs _ => true
              | ERecord xets => List.all (passive o #2) xets
              | EField (e, _) => passive e
              | _ => false

        fun exp env e =
            let
                (*val () = Print.prefaces "exp" [("e", MonoPrint.p_exp env (e, ErrorMsg.dummySpan))]*)

                fun doLet (x, t, e', b) =
                    let
                        fun doSub () =
                            let
                                val r = subExpInExp (0, e') b
                            in
                                (*Print.prefaces "doSub" [("e'", MonoPrint.p_exp env e'),
                                                        ("b", MonoPrint.p_exp (E.pushERel env x t NONE) b),
                                                        ("r", MonoPrint.p_exp env r)];*)
                                #1 (reduceExp env r)
                            end

                        fun trySub () =
                            ((*Print.prefaces "trySub"
                                            [("e", MonoPrint.p_exp env (e, ErrorMsg.dummySpan))];*)
                             case t of
                                 (TSignal _, _) => e
                               | _ =>
                                 case e' of
                                     (ECase _, _) => e
                                   | _ => doSub ())

                        fun isRecord () =
                            case #1 e' of
                                ERecord _ => true
                              | _ => false

                        fun prefixFrom i (e : exp) =
                            case #1 e of
                                ERel i' => if i' = i then SOME [] else NONE
                              | EField (e', s) =>
                                (case prefixFrom i e' of
                                     NONE => NONE
                                   | SOME ss => SOME (ss @ [s]))
                              | _ => NONE

                        fun whichProj i (e : exp) =
                            case #1 e of
                                EPrim _ => SOME SLS.empty
                              | ERel i' => if i' = i then NONE else SOME SLS.empty
                              | ENamed _ => SOME SLS.empty
                              | ECon (_, _, NONE) => SOME SLS.empty
                              | ECon (_, _, SOME e') => whichProj i e'
                              | ENone _ => SOME SLS.empty
                              | ESome (_, e') => whichProj i e'
                              | EFfi _ => SOME SLS.empty
                              | EFfiApp (_, _, es) => whichProjs i (map #1 es)
                              | EApp (e1, e2) => whichProjs i [e1, e2]
                              | EAbs (_, _, _, e) => whichProj (i + 1) e
                              | EUnop (_, e1) => whichProj i e1
                              | EBinop (_, _, e1, e2) => whichProjs i [e1, e2]
                              | ERecord xets => whichProjs i (map #2 xets)
                              | EField (e1, s) =>
                                (case prefixFrom i e1 of
                                     NONE => SOME SLS.empty
                                   | SOME ss => SOME (SLS.singleton (ss @ [s])))
                              | ECase (e1, pes, _) =>
                                whichProjs' i ((0, e1)
                                               :: map (fn (p, e) => (patBinds p, e)) pes)
                              | EStrcat (e1, e2) => whichProjs i [e1, e2]
                              | EError (e1, _) => whichProj i e1
                              | EReturnBlob {blob = NONE, mimeType = e2, ...} => whichProj i e2
                              | EReturnBlob {blob = SOME e1, mimeType = e2, ...} => whichProjs i [e1, e2]
                              | ERedirect (e1, _) => whichProj i e1
                              | EWrite e1 => whichProj i e1
                              | ESeq (e1, e2) => whichProjs i [e1, e2]
                              | ELet (_, _, e1, e2) => whichProjs' i [(0, e1), (1, e2)]
                              | EClosure (_, es) => whichProjs i es
                              | EQuery {query = e1, body = e2, initial = e3, ...} =>
                                whichProjs' i [(0, e1), (2, e2), (0, e3)]
                              | EDml (e1, _) => whichProj i e1
                              | ENextval e1 => whichProj i e1
                              | ESetval (e1, e2) => whichProjs i [e1, e2]
                              | EUnurlify (e1, _, _) => whichProj i e1
                              | EJavaScript (_, e1) => whichProj i e1
                              | ESignalReturn e1 => whichProj i e1
                              | ESignalBind (e1, e2) => whichProjs i [e1, e2]
                              | ESignalSource e1 => whichProj i e1
                              | EServerCall (e1, _, _, _) => whichProj i e1
                              | ERecv (e1, _) => whichProj i e1
                              | ESleep e1 => whichProj i e1
                              | ESpawn e1 => whichProj i e1

                        and whichProjs i es =
                            whichProjs' i (map (fn e => (0, e)) es)

                        and whichProjs' i es =
                            case es of
                                [] => SOME SLS.empty
                              | (n, e) :: es' =>
                                case (whichProj (i + n) e, whichProjs' i es') of
                                    (SOME m1, SOME m2) =>
                                    if SLS.isEmpty (SLS.intersection (m1, m2)) then
                                        SOME (SLS.union (m1, m2))
                                    else
                                        NONE
                                  | _ => NONE
                    in
                        if impure env e' then
                            let
                                val effs_e' = summarize 0 e'
                                val effs_e' = List.filter (fn x => x <> UseRel) effs_e'
                                val effs_b = summarize 0 b

                                (*val () = Print.prefaces "Try"
                                                        [(*("e", MonoPrint.p_exp env (e, ErrorMsg.dummySpan)),*)
                                                         ("e'", MonoPrint.p_exp env e'),
                                                         ("b", MonoPrint.p_exp (E.pushERel env x t NONE) b),
                                                         ("e'_eff", p_events effs_e'),
                                                         ("b_eff", p_events effs_b)]*)

                                fun does eff = List.exists (fn eff' => eff' = eff) effs_e'
                                val writesPage = does WritePage
                                val readsDb = does ReadDb
                                val writesDb = does WriteDb
                                val readsCookie = does ReadCookie
                                val writesCookie = does ReadCookie

                                fun verifyUnused eff =
                                    case eff of
                                        UseRel => false
                                      | _ => true

                                fun verifyCompatible effs =
                                    case effs of
                                        [] => false
                                      | eff :: effs =>
                                        case eff of
                                            Unsure => false
                                          | UseRel => List.all verifyUnused effs
                                          | WritePage => not writesPage andalso verifyCompatible effs
                                          | ReadDb => not writesDb andalso verifyCompatible effs
                                          | WriteDb => not writesDb andalso not readsDb andalso verifyCompatible effs
                                          | ReadCookie => not writesCookie andalso verifyCompatible effs
                                          | WriteCookie => not writesCookie andalso not readsCookie
                                                           andalso verifyCompatible effs
                                          | Abort => true
                            in
                                (*Print.prefaces "verifyCompatible"
                                                 [("e'", MonoPrint.p_exp env e'),
                                                  ("b", MonoPrint.p_exp (E.pushERel env x t NONE) b),
                                                  ("effs_e'", Print.p_list p_event effs_e'),
                                                  ("effs_b", Print.p_list p_event effs_b)];*)
                                if (List.null effs_e'
                                    orelse (List.all (fn eff => eff <> Unsure) effs_e'
                                            andalso verifyCompatible effs_b)
                                    orelse (case effs_b of
                                                UseRel :: effs => List.all verifyUnused effs
                                              | _ => false))
                                   andalso countFree 0 0 b = 1
                                   andalso not (freeInAbs b) then
                                    trySub ()
                                else
                                    e
                            end
                        else if countFree 0 0 b > 1
                                andalso not (!fullMode)
                                andalso not (passive e')
                                andalso not (isRecord () andalso Option.isSome (whichProj 0 b)) then
                            e
                        else
                            trySub ()
                    end

                val r =
                    case e of
                        ERel n =>
                        (case E.lookupERel env n of
                             (_, _, SOME e') => #1 e'
                           | _ => e)
                      | ENamed n =>
                        (case E.lookupENamed env n of
                             (_, _, SOME e', _) => ((*Print.prefaces "Switch" [("n", Print.PD.string (Int.toString n)),
                                                                               ("e'", MonoPrint.p_exp env e')];*)
                                                    #1 e')
                           | _ => e)

                      | EApp ((EAbs (x, t, _, e1), loc), e2) =>
                        ((*Print.prefaces "Considering" [("e1", MonoPrint.p_exp (E.pushERel env x t NONE) e1),
                                                       ("e2", MonoPrint.p_exp env e2),
                                                       ("sub", MonoPrint.p_exp env (reduceExp env (subExpInExp (0, e2) e1)))];*)
                         if impure env e2 orelse (not (!fullMode) andalso countFree 0 0 e1 > 1) then
                             #1 (reduceExp env (ELet (x, t, e2, e1), loc))
                         else
                             #1 (reduceExp env (subExpInExp (0, e2) e1)))

                      | ECase (e', pes, {disc, result}) =>
                        let
                            fun push () =
                                case result of
                                    (TFun (dom, result), loc) =>
                                    let
                                        fun safe e =
                                            List.all (fn UseRel => true
                                                       | Abort => true
                                                       | _ => false) (summarize 0 e)

                                        fun p_events' es = Print.box [Print.PD.string "{",
                                                                      p_events es,
                                                                      Print.PD.string "}"]
                                    in
                                        if List.all (safe o #2) pes then
                                            (yankedCase := true;
                                             EAbs ("y", dom, result,
                                                   (ECase (liftExpInExp 0 e',
                                                           map (fn (p, (EAbs (_, _, _, e), _)) =>
                                                                   (p, swapExpVarsPat (0, patBinds p) e)
                                                               | (p, (EError (e, (TFun (_, t), _)), loc)) =>
                                                                 (p, (EError (liftExpInExp (patBinds p) e, t), loc))
                                                               | (p, e) =>
                                                                 (p, (EApp (liftExpInExp (patBinds p) e,
                                                                            (ERel (patBinds p), loc)), loc)))
                                                               pes,
                                                           {disc = disc, result = result}), loc)))
                                        else
                                            e
                                    end
                                  | _ => e

                            fun search pes =
                                case pes of
                                    [] => push ()
                                  | (p, body) :: pes =>
                                    case match ([], p, e') of
                                        No => search pes
                                      | Maybe => push ()
                                      | Yes subs =>
                                        let
                                            val (body, remaining) =
                                                foldl (fn ((x, t, e), (body, remaining)) =>
                                                          (if countFree 0 0 body > 1 then
                                                               (ELet (x, t, multiLift remaining e, body), #2 e')
                                                           else
                                                               subExpInExp (0, multiLift remaining e) body, remaining - 1))
                                                      (body, length subs - 1) subs
                                            val r = reduceExp (E.patBinds env p) body
                                        in
                                            (*Print.preface ("subs", Print.p_list (MonoPrint.p_exp env) subs);*)
                                            (*Print.prefaces "ECase"
                                                           [("old", MonoPrint.p_exp env body),
                                                            ("body", MonoPrint.p_exp env body),
                                                            ("r", MonoPrint.p_exp env r)];*)
                                            #1 r
                                        end
                        in
                            if impure env e' then
                                e
                            else
                                search pes
                        end

                      | EField (e1, x) =>
                        let
                            fun yankLets (e : exp) =
                                case #1 e of
                                    ELet (x, t, e1, e2) => (ELet (x, t, e1, yankLets e2), #2 e)
                                  | ERecord xes =>
                                    (case List.find (fn (x', _, _) => x' = x) xes of
                                         SOME (_, e, _) => e
                                       | NONE => (EField (e, x), #2 e))
                                  | _ => (EField (e, x), #2 e)
                        in
                            #1 (yankLets e1)
                        end

                      | ELet (x1, t1, (ELet (x2, t2, e1, b1), loc), b2) =>
                        let
                            val e' = (ELet (x2, t2, e1,
                                            (ELet (x1, t1, b1,
                                                   liftExpInExp 1 b2), loc)), loc)
                        in
                            (*Print.prefaces "ELet commute" [("e", MonoPrint.p_exp env (e, loc)),
                                                             ("e'", MonoPrint.p_exp env e')];*)
                            #1 (reduceExp env e')
                        end
                      | EApp ((ELet (x, t, e, b), loc), e') =>
                        #1 (reduceExp env (ELet (x, t, e,
                                                 (EApp (b, liftExpInExp 0 e'), loc)), loc))

                      | ELet (x, t, e', b as (EAbs (x', t' as (TRecord [], _), ran, e''), loc)) =>
                        if impure env e' then
                            doLet (x, t, e', b)
                        else
                            EAbs (x', t', ran, reduceExp (E.pushERel env x' t' NONE)
                                                         (ELet (x, t, liftExpInExp 0 e', swapExpVars 0 e''), loc))

                      | ELet (x, t, e', b) => doLet (x, t, e', b)

                      | EStrcat ((EPrim (Prim.String (k1, s1)), _), (EPrim (Prim.String (k2, s2)), _)) =>
                        EPrim (Prim.String ((case (k1, k2) of
                                                 (Prim.Html, Prim.Html) => Prim.Html
                                               | _ => Prim.Normal), s1 ^ s2))

                      | ESignalBind ((ESignalReturn e1, loc), e2) =>
                        #1 (reduceExp env (EApp (e2, e1), loc))

                      | _ => e
            in
                (*Print.prefaces "exp'" [("e", MonoPrint.p_exp env (e, ErrorMsg.dummySpan)),
                                       ("r", MonoPrint.p_exp env (r, ErrorMsg.dummySpan))];*)
                r
            end

        and bind (env, b) =
            case b of
                U.Decl.Datatype (x, n, xncs) => E.pushDatatype env x n xncs
              | U.Decl.RelE (x, t) => E.pushERel env x t NONE
              | U.Decl.NamedE (x, n, t, eo, s) =>
                let
                    val eo = case eo of
                                 NONE => NONE
                               | SOME e => if mayInline (n, e, t, s) then
                                               SOME e
                                           else
                                               NONE
                in
                    E.pushENamed env x n t (Option.map (reduceExp env) eo) s
                end

        and reduceExp env = U.Exp.mapB {typ = typ, exp = exp, bind = bind} env

        fun decl env d = ((*Print.preface ("d", MonoPrint.p_decl env (d, ErrorMsg.dummySpan));*)
                          d)
    in
        U.File.mapB {typ = typ, exp = exp, decl = decl, bind = bind} E.empty file
    end

fun doReduce file =
    let
        val () = yankedCase := false
        val file' = reduce' file
    in
        if !yankedCase then
            doReduce file'
        else
            file'
    end

val printDebug = ref false
fun setPrintDebug b =
    printDebug := b
fun trace (phase: string) (b: bool): bool =
    if b orelse not (!printDebug)
    then true
    else (TextIO.print ("Not equal: " ^ phase ^ "\n"); false)

fun existsInMap (m: IS.set IM.map, i: int, j: int): bool =
    case IM.find (m, i) of
        NONE => false
      | SOME set => IS.member (set, j)

fun findFirstInMap (m: IS.set IM.map, i: int): int option = 
    case IM.find (m, i) of
        NONE => NONE
      | SOME set => IS.find (fn _ => true) set

fun pushIntoMap (m: IS.set IM.map, i: int, j: int): IS.set IM.map = 
    case IM.find (m, i) of
        NONE => IM.insert (m, i, IS.singleton j)
      | SOME set => IM.insert (m, i, IS.add (set, j))

fun unionMaps (m1: IS.set IM.map, m2: IS.set IM.map): IS.set IM.map = 
    IM.unionWith IS.union (m1, m2)

fun debugMap (m1: IS.set IM.map): unit =
    if !printDebug
    then 
        List.app
            (fn (i, set) =>
                ( TextIO.print (Int.toString i ^ " - " )
                ; List.app (fn j => TextIO.print (Int.toString j ^ " ")) (IS.listItems set)
                ; TextIO.print "."))
            (IM.listItemsi m1)
    else ()
        
fun compareType (datatypeMapping: IS.set IM.map) (old: typ) (new: typ): bool =  
    let
        val recurse = compareType datatypeMapping
    in
    case (#1 old, #1 new) of
        (TFun (oldT1, oldT2), TFun (newT1, newT2)) => recurse oldT1 newT1 andalso recurse oldT2 newT2
      | (TRecord oldFields, TRecord newFields) =>
        ListPair.allEq
            (fn (oldF, newF) => #1 oldF = #1 newF andalso recurse (#2 oldF) (#2 newF))
            (oldFields, newFields)
      | (TDatatype (oldI, _), TDatatype (newI, _)) =>
        trace
            ("TDatatype: " ^ Int.toString oldI ^ " - " ^ Int.toString newI)
            (existsInMap (datatypeMapping, oldI, newI))
      | (TFfi (oldStr1, oldStr2), TFfi (newStr1, newStr2)) =>
        oldStr1 = newStr1 andalso oldStr2 = newStr2
      | (TOption oldT, TOption newT) => recurse oldT newT
      | (TList oldT, TList newT) => recurse oldT newT
      | (TSource, TSource) => true
      | (TSignal oldT, TSignal newT) => recurse oldT newT
      | _ => false
    end

fun compareCachedVal (m: mapping) (old: exp) (new: exp): bool =
    let
        val recurse = compareCachedVal m
        val recurseList = compareCachedValList m
    in
        case (#1 old, #1 new) of
            (EPrim old, EPrim new) => Prim.equal (old, new)
          | (ERel oldN, ERel newN) =>
            (* We're only caching top-level decl's, so Rel's will always have the same sequence numbers across runs. *)
            (* We're also comparing the function bodies, so if Rel's have the same seq number they are the same variable in the same function *)
            trace
                ("Rel: " ^ Int.toString oldN ^ " - " ^ Int.toString newN)
                (oldN = newN)
          | (ENamed oldN, ENamed newN) =>
            (* Check if referenced named bindings are the same *)
            trace
                ("Named = " ^ Int.toString oldN ^ " - " ^ Int.toString newN)
                (existsInMap (#named m, oldN, newN))
          | (ECon (_, PConVar oldN, oldEo), ECon (_, PConVar newN, newEo)) =>
            (* Check if referenced datatype constructors are the same *)
            trace
                ("Con with PConVar: " ^ Int.toString oldN ^ " - " ^ Int.toString newN)
                (existsInMap (#constructors m, oldN, newN)
                 andalso
                 (* Check if expressions inside are the same *)
                 (case (oldEo, newEo) of
                      (SOME oldE', SOME newE') =>
                      recurse oldE' newE'
                    | (NONE, NONE) => true
                    | _ => false))
          | (ECon (_, PConFfi oldFfi, oldEo), ECon (_, PConFfi newFfi, newEo)) =>
            (* Check if referenced FFI constructor names are the same *)
            trace
                ("Con with PConFfi: "
                 ^ #mod oldFfi ^ "/" ^ #datatyp oldFfi ^ "." ^ #con oldFfi ^ " - "
                 ^ #mod newFfi ^ "/" ^ #datatyp newFfi ^ "." ^ #con newFfi)
                (#mod oldFfi = #mod newFfi
                 andalso #datatyp oldFfi = #datatyp newFfi
                 andalso #con oldFfi = #con newFfi
                 andalso
                 (* Check if expressions inside are the same *)
                 (case (oldEo, newEo) of
                      (SOME oldE', SOME newE') =>
                      recurse oldE' newE'
                    | (NONE, NONE) => true
                    | _ => false
                ))
          | (ENone oldT, ENone newT) => compareType (#datatypes m) oldT newT
          | (ESome (oldT, oldE), ESome (newT, newE)) =>
            compareType (#datatypes m) oldT newT
            andalso
            recurse oldE newE
          | (EFfi (oldS1, oldS2), EFfi (newS1, newS2)) =>
            oldS1 = newS1 andalso oldS2 = newS2
          | (EFfiApp (oldS1, oldS2, oldExps), EFfiApp (newS1, newS2, newExps)) =>
            (* Check if FFI references are the same and all arguments are *)
            oldS1 = newS1
            andalso oldS2 = newS2
            andalso ListPair.allEq (fn (oldT, newT) => compareType (#datatypes m) oldT newT) (List.map #2 oldExps, List.map #2 newExps)
            andalso recurseList (List.map #1 oldExps) (List.map #1 newExps)
          | (EApp (oldE1, oldE2), EApp (newE1, newE2)) =>
            recurse oldE1 newE1
            andalso recurse oldE2 newE2
          | (EAbs (oldStr, oldT1, oldT2, oldE), EAbs (newStr, newT1, newT2, newE)) =>
            oldStr = newStr
            andalso compareType (#datatypes m) oldT1 newT1
            andalso compareType (#datatypes m) oldT2 newT2
            andalso recurse oldE newE
          | (EUnop (oldStr, oldE), EUnop (newStr, newE)) =>
            oldStr = newStr
            andalso recurse oldE newE
          | (EBinop (_, oldStr, oldE1, oldE2), EBinop (_, newStr, newE1, newE2)) =>
            oldStr = newStr
            andalso recurse oldE1 newE1
            andalso recurse oldE2 newE2
          | (ERecord oldFields, ERecord newFields) =>
            (* First we compare record field labels, then value expressions inside *)
            List.map #1 oldFields = List.map #1 newFields
            andalso ListPair.allEq (fn (oldT, newT) => compareType (#datatypes m) oldT newT) (List.map #3 oldFields, List.map #3 newFields)
            andalso recurseList (List.map #2 oldFields) (List.map #2 newFields)
          | (EField (oldE, oldStr), EField (newE, newStr)) =>
            oldStr = newStr
            andalso recurse oldE newE
          | (ECase (oldE, oldPatterns, {disc = oldT1, result = oldT2}), ECase (newE, newPatterns, {disc = newT1, result = newT2})) =>
            let
                val res1 = recurse oldE newE
                val res2 = let
                    (* Check if all patterns are the same *)
                    fun comparePattern (oldP: pat) (newP: pat): bool = 
                        case (#1 oldP, #1 newP) of
                            (PVar (oldName, oldT), PVar (newName, newT)) =>
                            compareType (#datatypes m) oldT newT
                          | (PPrim oldP, PPrim newP) =>
                            Prim.equal (oldP, newP)
                          | (PCon (_, _, NONE), PCon (_, _, NONE)) => true
                          | (PCon (_, oldPatCon, SOME oldPo), PCon (_, newPatCon, SOME newPo)) =>
                            (case (oldPatCon, newPatCon) of
                                 (PConVar oldN, PConVar newN) =>
                                 existsInMap (#constructors m, oldN, newN)
                               | (PConFfi oldFfi, PConFfi newFfi) => 
                                 #mod oldFfi = #mod newFfi
                                 andalso #datatyp oldFfi = #datatyp newFfi
                                 andalso #con oldFfi = #con newFfi
                               | _ => false)
                            andalso comparePattern oldPo newPo
                          | (PRecord oldPs, PRecord newPs) =>
                            ListPair.allEq
                                (fn (oldP, newP) =>
                                    #1 oldP = #1 newP
                                    andalso compareType (#datatypes m) (#3 oldP) (#3 newP)
                                    andalso comparePattern (#2 oldP) (#2 newP))
                                (oldPs, newPs)                            
                          | (PNone oldT, PNone newT) => compareType (#datatypes m) oldT newT
                          | (PSome (oldT, oldP'), PSome (newT, newP')) =>
                            compareType (#datatypes m) oldT newT
                            andalso comparePattern oldP' newP'
                          | _ => false
                in
                    ListPair.allEq
                        (fn ((oldP, oldE), (newP, newE)) =>
                            comparePattern oldP newP
                            andalso recurse oldE newE
                        )
                        (oldPatterns, newPatterns)
                end
                val res3 = compareType (#datatypes m) oldT1 newT1
                val res4 = compareType (#datatypes m) oldT2 newT2
            in
                res1 andalso res2 andalso res3 andalso res4
            end
          | (EStrcat (oldE1, oldE2), EStrcat (newE1, newE2)) =>
            recurse oldE1 newE1
            andalso recurse oldE2 newE2
          | (EError (oldE, oldT), EError (newE, newT)) =>
            compareType (#datatypes m) oldT newT
            andalso
            recurse oldE newE
          | (EReturnBlob {blob = NONE, mimeType = oldME, t = oldT}, EReturnBlob {blob = NONE, mimeType = newME, t = newT}) =>
            compareType (#datatypes m) oldT newT
            andalso
            recurse oldME newME
          | (EReturnBlob {blob = SOME oldBE, mimeType = oldME, ...}, EReturnBlob {blob = SOME newBE, mimeType = newME, ...}) =>
            recurse oldME newME
            andalso recurse oldBE newBE
          | (ERedirect (oldE, oldT), ERedirect (newE, newT)) => 
            compareType (#datatypes m) oldT newT
            andalso recurse oldE newE
          | (EWrite oldE, EWrite newE) =>
            recurse oldE newE
          | (ESeq (oldE1, oldE2), ESeq (newE1, newE2)) =>
            recurse oldE1 newE1
            andalso recurse oldE2 newE2
          | (ELet (oldName, oldT, oldE1, oldE2), ELet (newName, newT, newE1, newE2)) =>
            recurse oldE1 newE1
            andalso compareType (#datatypes m) oldT newT
            andalso recurse oldE2 newE2
          | (EClosure (_, oldExps), EClosure (_, newExps)) =>
            recurseList oldExps newExps
          | (EQuery {query = oldQuery, body = oldBody, initial = oldInitial, ...}, EQuery {query = newQuery, body = newBody, initial = newInitial, ...}) =>
            recurse oldQuery newQuery
            andalso recurse oldBody newBody
            andalso recurse oldInitial newInitial
          | (EDml (oldE, oldFm), EDml (newE, newFm)) =>
            oldFm = newFm
            andalso recurse oldE newE
          | (ENextval oldE, ENextval newE) => 
            recurse oldE newE
          | (ESetval (oldE1, oldE2), ESetval (newE1, newE2)) =>
            recurse oldE1 newE1
            andalso recurse oldE2 newE2
          | (EUnurlify (oldE, oldT, oldB), EUnurlify (newE, newT, newB)) =>
            oldB = newB
            andalso compareType (#datatypes m) oldT newT
            andalso recurse oldE newE
          | (EJavaScript (oldJm, oldE), EJavaScript (newJm, newE)) =>
            (case (oldJm, newJm) of
                 (Attribute, Attribute) => true
               | (Script, Script) => true
               | (Source t1, Source t2) => compareType (#datatypes m) t1 t2
               | _ => false)
            andalso recurse oldE newE
          | (ESignalReturn oldE, ESignalReturn newE) =>
            recurse oldE newE
          | (ESignalBind (oldE1, oldE2), ESignalBind (newE1, newE2)) =>
            recurse oldE1 newE1
            andalso recurse oldE2 newE2
          | (ESignalSource oldE, ESignalSource newE) =>
            recurse oldE newE
          | (EServerCall (oldE, oldT, _, oldFm), EServerCall (newE, newT, _, newFm)) =>
            oldFm = newFm
            andalso compareType (#datatypes m) oldT newT
            andalso recurse oldE newE
          | (ERecv (oldE, oldT), ERecv (newE, newT)) =>
            compareType (#datatypes m) oldT newT
            andalso recurse oldE newE
          | (ESleep oldE, ESleep newE) =>
            recurse oldE newE
          | (ESpawn oldE, ESpawn newE) =>
            recurse oldE newE
          | _ => false
    end

and compareCachedValList (m: mapping) (oldExps: exp list) (newExps: exp list) : bool =
    ListPair.allEq
        (fn (oldE, newE) => compareCachedVal m oldE newE)
        (oldExps, newExps)

(* TODO: make a map from int -> refs, where int = (old) number of datatype, to make lookup faster *)
val updatedRefs = (ref [] : (((datatype_kind * (string * int * typ option) list) ref) list) ref)
fun updateTyp (m: mapping) (t: typ): typ = 
    (case #1 t of
         TDatatype (j, r) =>
         let
             val newJ = 
                 case findFirstInMap (#datatypes m, j) of
                     NONE => raise Fail ("Datatype - updateTyp: No mapping found for " ^ Int.toString j)
                   | SOME newJ => newJ
         in
             ( if List.exists (fn r' => r' = r) (!updatedRefs)
               then ()
               else
                   let
                       val () = updatedRefs := (r :: (!updatedRefs))
                       val oldDtKind = #1 (!r)
                       val oldConstrs = #2 (!r)
                       val newConstrs =
                           List.map (fn (str, j, to) => (str
                                                        , case findFirstInMap (#constructors m, j) of
                                                              NONE => raise Fail ("Constructor: No mapping found for " ^ Int.toString j)
                                                            | SOME newJ => newJ
                                                        (* MonoUtil doesn't descend here since we're in a ref so doing it explicitely *)
                                                        , Option.map (U.Typ.map (fn t' => #1 (updateTyp m (t', ErrorMsg.dummySpan)))) to
                                    )) oldConstrs
                   in
                       r := (oldDtKind, newConstrs)
                   end
             ; TDatatype (newJ, r))
         end
       | t' => t'
    , #2 t)

fun updatePat (m: mapping) (pat: pat): pat =
    (case #1 pat of
        PCon (dtk, PConVar j, po) =>
        let
            val newJ = case findFirstInMap (#constructors m, j) of
                           NONE => raise Fail ("Datatype: No mapping found for " ^ Int.toString j)
                         | SOME newJ => newJ
        in
            PCon (dtk, PConVar newJ, Option.map (updatePat m) po)
        end
        | PRecord fields => PRecord (List.map (fn (str, pat, typ) => (str, updatePat m pat, typ)) fields)
        | PSome (t, pat) => PSome (t, updatePat m pat)
        | p => p
    , #2 pat)

fun updateExp (m: mapping) (e: exp): exp =
    (case #1 e of
        ENamed j => (case findFirstInMap (#named m, j) of
                         NONE => raise Fail ("ENamed = No mapping found for " ^ Int.toString j)
                       | SOME newJ => ENamed newJ)
      | ECon (dt, PConVar j, eo) =>
        let
            val newJ = case findFirstInMap (#constructors m, j) of
                           NONE => raise Fail ("ECon: No mapping found for " ^ Int.toString j)
                         | SOME newJ => newJ
        in
            ECon (dt, PConVar newJ, eo)
        end
      | ECase (e, pats, t) =>
        let
            val newpats = List.map (fn (p, e) => (updatePat m p , e)) pats
        in
            ECase (e, newpats, t)
        end
      | e => e, #2 e)
    
fun updateCachedVal (m: mapping) (e: exp): exp =
    U.Exp.map
        { typ = fn t => #1 (updateTyp m (t, ErrorMsg.dummySpan))
        , exp = fn e => #1 (updateExp m (e, ErrorMsg.dummySpan))
        }
        e

fun printnames (f: file) =
    ( List.app (fn (d, _) => case d of DVal v => TextIO.print (#1 v ^ " #" ^ Int.toString (#2 v) ^ " " ^ (#5 v) ^"\n")
                                     | DValRec vals => List.app (fn v => TextIO.print (#1 v ^ " #" ^ Int.toString (#2 v) ^ " " ^ (#5 v) ^"\n")) vals
                                     | _ => ()) (#1 f)
    ; TextIO.print "\n")

fun debug (s: string) (value: 'a): 'a =
    if !printDebug
    then (TextIO.print s; value)
    else value

fun debugP (preface: string) (p: Print.PD.pp_desc) (value: 'a): 'a =
    if !printDebug
    then (Print.preface (preface, p); TextIO.flushOut TextIO.stdOut; value)
    else value

fun reduce (file: file) (optim: bool) =
    let
        (* val () = if not optim then () else printnames file *)
        (* val () = if not optim then () else Print.preface ("full file: ", (MonoPrint.p_file E.empty file)) *)
        val () = updatedRefs := []
        val prevVals = !cachedVals
        val prevValRecs = !cachedValRecs
        val prevDatatypes = !cachedDatatypes
        val compareTimer = Timer.startCPUTimer ()
        val (newDecls, _) =
            if not optim
            then (List.rev (#1 file), { constructors = IM.empty
                                      , named = IM.empty
                                      , datatypes = IM.empty })
            else
            (* Walking over all decls in file:
             * * If Vals or ValRecs are the same as previously, and their deps are, use the optimized version instead
             * * Save mappings between sequence numbers (for Named bindings and datatype bindings) if they're the same, these are used in the comparisons
             *)
            List.foldl
                (fn (decl, (decls: decl list, m: mapping)) =>
                    case #1 decl of
                        DVal (name, i, t, e, fullname) =>
                        let
                            val () = debug ("DVal " ^ Int.toString i ^ " " ^ name ^ ". ") ()
                            (* val () = Print.preface ((name ^" :: "), (MonoPrint.p_typ E.empty t)) *)
                            (* val () = TextIO.flushOut TextIO.stdOut *)
                            val foundByName = List.filter (fn v => #name v = name andalso #fullname v = fullname) prevVals (* names are not always unique, sometimes blank (?) => filter *)
                            val foundByComparison = List.filter (fn v => compareCachedVal m (#orig v) e
                                                                         andalso compareType (#datatypes m) (#typ v) t)
                                                                foundByName
                        in
                            case foundByComparison of
                                [] => (debug ("  No hit.\n") (decl :: decls, m))
                              | cacheds => 
                                let
                                    val newmapping = List.foldl (fn (cached, acc) => pushIntoMap (acc, #seqNum cached, i)) IM.empty cacheds
                                    val () = debug "\n  Hit. Mapping: " ()
                                    val () = debugMap newmapping
                                    val () = debug "\n" ()
                                in
                                    ( (DVal (name, i, t, updateCachedVal m (#optim (List.hd cacheds)), fullname), #2 decl) :: decls
                                    , { named = unionMaps (newmapping, #named m)
                                      , datatypes = #datatypes m 
                                      , constructors = #constructors m 
                                      })
                                end
                        end
                     | DValRec vals => 
                       let
                           val () = debug "DValRec " ()
                           val () = List.app (fn v => debug ("#" ^ Int.toString (#2 v) ^ " " ^ #5 v ^ " ") ()) vals
                           (* val () = List.app (fn v => debugP "" (MonoPrint.p_typ E.empty (#3 v)) ()) vals *)
                           val foundByName = List.filter (fn prev => List.map #name prev = List.map #1 vals andalso
                                                                     List.map #fullname prev = List.map #5 vals) prevValRecs
                           (* We sometimes have 100% duplicates so we use filter instead of find *)
                           val foundByComparison =
                               List.filter (fn prev =>
                                               let
                                                   val extraMapping = ListPair.foldl (fn (new, cached, acc) => pushIntoMap (acc, #seqNum cached, #2 new)) IM.empty (vals, prev)
                                               in
                                                   ListPair.allEq (fn (new, cached) => compareCachedVal
                                                                                           { named = unionMaps (extraMapping, #named m)
                                                                                           , constructors = #constructors m
                                                                                           , datatypes = #datatypes m
                                                                                           }
                                                                                           (#orig cached) (#4 new)
                                                                                       andalso compareType (#datatypes m) (#typ cached) (#3 new))
                                                                  (vals, prev)
                                               end
                                           )
                                           foundByName
                       in
                           case foundByComparison of
                               [] => debug
                                         "  No hit.\n"
                                         (decl :: decls, m)
                             | cacheds => 
                               let
                                   val extraMapping =
                                       List.foldl
                                           (fn (cached, acc) =>
                                               ListPair.foldl (fn (new, cached', acc) => pushIntoMap (acc, #seqNum cached', #2 new)) acc (vals, cached))
                                           IM.empty
                                           cacheds
                                   val () = debug "\n  Hit. " ()
                                   val () = debug "RecVal mapping: " ()
                                   val () = debugMap extraMapping
                                   val () = debug "\n" ()
                               in
                                   ( ( DValRec (ListPair.map (fn ((x, i, t, _, n), cached) =>
                                                                 (x, i, t, updateCachedVal
                                                                               { named = unionMaps (extraMapping, #named m)
                                                                               , constructors = #constructors m
                                                                               , datatypes = #datatypes m
                                                                               }
                                                                               (#optim cached), n)) (vals, List.hd cacheds))
                                     , #2 decl )
                                     :: decls
                                   , { named = unionMaps (extraMapping, #named m)
                                     , constructors = #constructors m
                                     , datatypes = #datatypes m
                                     }
                                   )
                               end
                       end
                     | DDatatype (ds as (_ :: _)) =>
                       let 
                           val () = debug ("DDatatype: ") ()
                           val () = List.app (fn d => ( debug (#1 d ^ " #" ^ Int.toString (#2 d) ^ " ") ()
                                                      (* ; List.app (fn c => *)
                                                      (*                ( Print.preface ( #1 c ^ " :: " *)
                                                      (*                                , case #3 c of *)
                                                      (*                                      NONE => Print.PD.string "NONE" *)
                                                      (*                                    | SOME t => MonoPrint.p_typ E.empty t) *)
                                                      (*                ; TextIO.flushOut TextIO.stdOut) *)
                                                      (*            ) *)
                                                      (*            (#3 d) *)
                                                      )
                                             ) ds
                           val (constrMapping', datatypeMapping') =
                               let
                                   val foundByName = List.filter (fn prevds => List.map #name prevds = List.map #1 ds) prevDatatypes
                                   val foundByComparison =
                                       List.filter (fn saved =>
                                                       let
                                                           val ownMapping = ListPair.foldl
                                                                                (fn (oldD, newD, acc) => pushIntoMap (acc, #seqNum oldD, #2 newD))
                                                                                IM.empty
                                                                                (saved, ds)
                                                       in
                                                           ListPair.allEq
                                                               (fn (oldD, newD) =>
                                                                   ListPair.allEq (fn (oldC, newC) =>
                                                                                      #1 oldC = #1 newC
                                                                                      andalso (case (#3 oldC, #3 newC) of
                                                                                                   (NONE, NONE) => true
                                                                                                 | (SOME t1, SOME t2) =>
                                                                                                   compareType (unionMaps (ownMapping, #datatypes m)) t1 t2
                                                                                                 | _ => false))
                                                                                  (#constructors oldD, #3 newD))
                                                               (saved, ds)
                                                       end
                                                   )
                                                   foundByName
                               in
                                   case foundByComparison of
                                       [] => debug ("Nothing found for datatype\n") (IM.empty, IM.empty)
                                     | saveds =>
                                       let
                                           val constrMapping =
                                               List.foldl
                                                   (fn (saved, acc) =>
                                                       ListPair.foldl
                                                           (fn (oldD, newD, acc) =>
                                                               ListPair.foldl
                                                                   (fn (oldC, newC, acc) => pushIntoMap (acc, #2 oldC, #2 newC))
                                                                   acc
                                                                   (#constructors oldD, #3 newD))
                                                           acc
                                                           (saved, ds))
                                                   IM.empty
                                                   saveds
                                           val ownMapping =
                                               List.foldl
                                                   (fn (saved, acc) =>
                                                       ListPair.foldl
                                                           (fn (oldD, newD, acc) => pushIntoMap(acc,#seqNum oldD, #2 newD))
                                                           acc
                                                           (saved, ds))
                                                   IM.empty
                                                   saveds
                                           val () = debug "\n  Mapping: " ()
                                           val () = debugMap ownMapping
                                           val () = debug " | | | " ()
                                           val () = debug "Constructors mapping: " ()
                                           val () = debugMap constrMapping
                                           val () = debug "\n" ()
                                       in
                                           ( constrMapping , ownMapping)
                                       end
                               end
                       in
                           (decl :: decls
                           , { named = #named m
                             , constructors = unionMaps (constrMapping', #constructors m)
                             , datatypes = unionMaps (datatypeMapping', #datatypes m)
                             })
                       end
                     | _ => (decl :: decls, m)
                )
                ([], { constructors = IM.empty
                     , named = IM.empty
                     , datatypes = IM.empty})
                (#1 file)
        val file' = (List.rev newDecls, #2 file)
        val compareTime = Time.toMilliseconds (#usr (Timer.checkCPUTimer compareTimer))
        val () = if not optim then () else TextIO.print ("Comparetime: " ^ LargeInt.toString compareTime ^ "ms\n")
        val reduceTimer = Timer.startCPUTimer ()
        val res = doReduce file'
        val reduceTime = Time.toMilliseconds (#usr (Timer.checkCPUTimer reduceTimer))
        val () = if not optim then () else TextIO.print ("Reducetime: " ^ LargeInt.toString reduceTime ^ "ms\n")
        (* val () = List.app (fn d => Print.preface ("", (MonoPrint.p_decl E.empty d))) (#1 res) *)
        (* val () = TextIO.flushOut TextIO.stdOut *)
        (* val () = if not optim then () else printnames res *)
        val () = if not optim
                 then ()
                 else
                     let 
                         val (vals, valRecs, datatypes) =
                             (* Save optimized versions of vals and valrecs, and save datatypes aswell so we can map the sequence numbers next iteration *)
                             ListPair.foldl (fn ((d1, _), (d2, _), (accvals, accrecvals, accdatatypes)) =>
                                                case (d1, d2) of
                                                    (DVal (name, i, t, orig, fullname), DVal (_, _, _, optim, _)) =>
                                                    ({name = name, fullname = fullname, seqNum = i, orig = orig, optim = optim, typ = t} :: accvals, accrecvals, accdatatypes)
                                                  | (DValRec origVals, DValRec optimVals) =>
                                                    ( accvals
                                                    , (ListPair.map (fn ((name, i, t, orig, fullname), (_, j, _, optim, _)) =>
                                                                        {name = name, fullname = fullname, seqNum = i, orig = orig, optim = optim, typ = t})
                                                                    (origVals, optimVals)) :: accrecvals
                                                    , accdatatypes)
                                                  | (DDatatype ds, _) => 
                                                    (accvals, accrecvals, (List.map (fn (name, i, cons) => {name = name, seqNum = i, constructors = cons}) ds) :: accdatatypes)
                                                  | _ => (accvals, accrecvals, accdatatypes)
                                            ) ([], [], []) (#1 file, #1 res)
                         val () = cachedVals := vals
                         val () = cachedValRecs := valRecs
                         val () = cachedDatatypes := datatypes
                     in 
                         ()
                     end
    in
        res
    end
end
