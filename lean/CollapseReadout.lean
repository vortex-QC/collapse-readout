/-
# 叠置裂解读出核 (R-1, R-2, R-3 · 2026-10-10)
对应: papers/叠置裂解命题_立项_v0.1.md §四 (主人三钉: A 交汇命题立项+R 系形式化随行+档名"叠置裂解命题")
上游: SuperpositionMeasure.lean 四件 (T_S1b/T_F1'-1/T_F1'-2/S-4·Diffuse 定义·2026-10-07)
体系: 随-2 线 (随机数学来源·主人定调"随机+维度共同前置柱")——
  「随机是动本身的描述」(随-1·采认);
  「叠置裂解=随机+维度共同前置柱」(随-2·柱定义升格采认);
  「动数的群体性从叠置态裂解来」(随-3·采认);
  「布朗随机性=动约束满态」+「裂解之后满态全域可读」(思维验证四钉③④采认).

语义锚 (体系层·不进形式层):
  - 叠置态 = Diffuse 测度 (采认等式: 叠置态的数轴显化=Diffuse 测度·结构面·群体性之源);
  - 裂解 = 读出事件 (许愿取出/测量公设/投影的统一事件名·事件面·个体性之源);
  - 随机 = 两件的张力: 个体不可取出 (单点零测) × 群体确定 (测度结构给定);
  - 裂解产物 = 由后果反定义 (锚-1); 测量史 = 原子堆积 (域型读法·每裂解一次种一个原子);
  - 群体预付/个体在线: 群体性预付在叠置态里, 个体性在线地在裂解里产生 (对偶命题两分).

形式内容 (三件·全部复用四件地基零新增困难·Mathlib 标准测度论):
  - R-1 裂解记录件: 可数读出集被单点原子族承载 (读数测度 ≤ 单点质量和) ——
    "测量史=原子堆积"的定理化: 裂解的每一次实现都记在一个原子账上;
  - R-2 个体不可预言件: Diffuse 测度下可数猜测集的补集满测 ——
    "随机=猜不中"的定理化: 无论怎么猜 (可数次) 猜中测度为零, 读数几乎必然在猜测之外;
  - R-3 裂解实现无痕件: Diffuse 测度下取出单点实现不改群体测度 ——
    "裂解只产生实现不改测度" (预付域读法) 的定理化: 实现不留痕于群体.
边界 (如实标): R 系=语义标注级小件 (复用四件地基)·原子的完整结构未展开 (同四件边界);
  翻译层纪律: 定理级 = 抽象结构内.
-/
import Mathlib
import DensityMath.SuperpositionMeasure

namespace Collapse

open Superposition

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X]
  {ν : MeasureTheory.Measure X}

/-- R-1 裂解记录件: 可数读出集被单点原子族承载 —— 读数集的测度全部记在单点原子账上
    ("测量史=原子堆积"的定理化: 每次裂解的实现 = 一个原子记录). -/
theorem collapse_atoms {s : Set X} (hs : s.Countable) :
    ∃ f : ℕ → X, ν s ≤ ∑' i : ℕ, ν {(f i : X)} := by
  obtain ⟨f, hf⟩ := Set.countable_iff_exists_subset_range.mp hs
  refine ⟨f, le_trans (MeasureTheory.measure_mono ?_) (MeasureTheory.measure_iUnion_le _)⟩
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_range.mp (hf hx)
  exact Set.mem_iUnion.mpr ⟨i, by simp [hi]⟩

/-- R-2 个体不可预言件: Diffuse 测度下, 任何可数猜测集的补集满测 ——
    "随机=猜不中"的定理化: 猜中测度为零 (countable_null), 读数几乎必然落在猜测之外. -/
theorem guess_missed (hd : Diffuse ν) {s : Set X} (hs : MeasurableSet s)
    (hc : s.Countable) : ν sᶜ = ν Set.univ := by
  have h0 : ν s = 0 := Superposition.countable_null hd hc
  have h := MeasureTheory.measure_union_add_inter (μ := ν) s hs.compl
  rw [Set.union_compl_self, Set.inter_compl_self, MeasureTheory.measure_empty] at h
  rw [h0, zero_add] at h
  simp only [add_zero] at h
  exact h.symm

/-- R-3 裂解实现无痕件: Diffuse 测度下, 取出单点实现不改群体测度 ——
    "裂解只产生实现不改测度" (群体预付/个体在线·预付域读法) 的定理化:
    实现不留痕于群体 (单点零测 = 取出的结构性无痕). -/
theorem collapse_traceless (hd : Diffuse ν) (x : X) {s : Set X} (hs : MeasurableSet s) :
    ν (insert x s) = ν s := by
  by_cases hx : x ∈ s
  · rw [Set.insert_eq_self.mpr hx]
  · have h := MeasureTheory.measure_union_add_inter (μ := ν) {x} hs
    rw [Set.inter_comm, Set.inter_singleton_eq_empty.mpr hx, MeasureTheory.measure_empty,
      hd x, zero_add] at h
    simpa using h

/-- R-4 裂解分布不变件: 概率测度下二次裂解的第一边缘 = 单次裂解分布 ——
    "裂解序列同分布" (iid 的边缘面) 的定理化: 群体测度结构是裂解序列的唯一承重,
    裂解不产生新分布 (群体预付·随-3). -/
theorem collapse_marginal [MeasureTheory.SFinite ν] (hν1 : ν Set.univ = 1) :
    MeasureTheory.Measure.map Prod.fst (ν.prod ν) = ν := by
  rw [MeasureTheory.Measure.map_fst_prod, hν1, one_smul]

end Collapse
