/-
# 叠置态测度核 (T_S1b, T_F1'-1, T_F1'-2, S-4 · 2026-10-07)
对应: papers/双端图景_数学域显化_连续测度_开放思考_v0.2.md §九 (主人精确化+两钉采认+形式化立项)
体系: 主人两轮开放思考定调——
  「双端图景的叠置态，在数轴上是成立的，我理解的，在数轴上的显化是连续测度」(P-c·采认①定版等式·定义名 Diffuse 主人钉 2026-10-07);
  「一般测度，是离散描述，有大小，距离等离散读数」(P-a·采认②域型读法: 原子型=测量堆积/连续型=结构给出);
  「在数轴上，无穷大，无穷小，以及极限都没有成本」(P-b·预付域的测度语义).

语义锚 (体系层·不进形式层):
  - 叠置态 = 双端图景失效线外的"挤在一起·无差"态 (物理域不可达·只能残影/拥挤);
  - 连续测度 (atomless) = 叠置态的数轴实现 (采认①): 单点零测 = 个体差的结构性不存在;
  - 原子型 = 物理测量读数的堆积 (离散读数格 = 原子·在线成本); 连续型 = 数轴 (零成本·结构给出) ——
    两域的差别 = 测度怎么被产生 (对偶命题在线/预付之分的测度语义);
  - 观测 = 许愿 (从叠置取出): 取出单点得零 (无差) / 取出正测度集得差 (有差) —— 观测粒度决定有差/无差.

形式内容 (四件·零公理纯展开·Mathlib 标准测度论):
  - T_S1b    可数零测件: atomless 测度下任何可数集零测 —— 叠置域上可数目标集全零测
             (主人实数轴论证的定理化: "随便指一个数恰为整数"概率为零);
  - T_F1'-2  纤维零测件: atomless 推映下单停点纤维 (原像) 零测 —— 一般位置纤维结构的测度化
             (归宿解释命题钉-1 "纤维测度结构" 真测度版);
  - T_F1'-1  离散读数原子件: 概率测度 + 可数值读出映射 → 推映必有正单点质量 (读数格 = 原子)
             —— P-a "一般测度是离散描述" 的定理化: 离散读数必然产生原子;
  - S-4      叠置需不可数读出面: 非零测度 + atomless 推映 → 读出值域不可数 —— P-c 的必然性定理化:
             叠置态 (atomless) 只能在不可数读出面 (数轴型连续统) 上成立.
边界 (如实标): 原子的完整结构 (不可分性定义) 未展开——本核以"正单点质量"为离散原子语义的
  操作化陈述; 连续测度与密度数学的 δ 对齐方向未判定; 翻译层纪律: 定理级 = 抽象结构内.
-/
import Mathlib

namespace Superposition

/-- 弥散测度 (Diffuse·主人钉名 2026-10-07): 每个单点零测 —— 个体差结构性不存在.
    学术对齐 (C7 溯源同日核验): diffuse = atomless/nonatomic/continuous measure 的标准同义词
    (Kallenberg《Random Measures》点过程学派主用; Billingsley《Probability and Measure》分解
    定理习题同款: 概率测度 = diffuse 部分 + 纯原子部分) —— 定义 = ∀x ν{x} = 0 (点连续版,
    有限测度下与 nonatomic 等价·无限测度下 nonatomic 更强·本核四件定理只用点连续性质)。
    体系共振 (对频非同一·防四态混读): 双端图景宏观端 = 弥散背景 E 端; 无边界是介质 =
    diffuse 的介质型语义; 叠置态的数轴显化 = 连续测度 (采认①等式)。
    体系语义 (叠置态/零成本/许愿) 为外挂锚·不进形式层。 -/
def Diffuse {X : Type*} [MeasurableSpace X] (ν : MeasureTheory.Measure X) : Prop := ∀ x : X, ν {x} = 0

variable {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]
  [MeasurableSingletonClass X] [Nonempty X] {μ : MeasureTheory.Measure H} {π : H → X}

/-- 公共件: 测度全域被可数单点族覆盖 ⟹ 全域测度 ≤ 单点质量级数 (枚举·两定理共用). -/
private theorem univ_le_tsum_enum (ν : MeasureTheory.Measure X)
    (hcu : (Set.univ : Set X).Countable) :
    ∃ f : ℕ → X, ν Set.univ ≤ ∑' i : ℕ, ν {(f i : X)} := by
  obtain ⟨f, hf⟩ := Set.countable_iff_exists_subset_range.mp hcu
  refine ⟨f, le_trans (MeasureTheory.measure_mono ?_) (MeasureTheory.measure_iUnion_le _)⟩
  intro x _
  obtain ⟨i, hi⟩ := Set.mem_range.mp (hf (Set.mem_univ x))
  exact Set.mem_iUnion.mpr ⟨i, by simp [hi]⟩

/-- T_S1b 可数零测件 (叠置域): atomless 测度下任何可数集零测 —— 可数目标集
    (如数轴上的整数集) 在叠置域上全部无差 —— 主人实数轴论证的定理化. -/
theorem countable_null {ν : MeasureTheory.Measure X} (hd : Diffuse ν)
    {s : Set X} (hs : s.Countable) : ν s = 0 := by
  obtain ⟨f, hf⟩ := Set.countable_iff_exists_subset_range.mp hs
  have hle : ν s ≤ ∑' i : ℕ, ν {(f i : X)} := by
    refine le_trans (MeasureTheory.measure_mono ?_) (MeasureTheory.measure_iUnion_le _)
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_range.mp (hf hx)
    exact Set.mem_iUnion.mpr ⟨i, by simp [hi]⟩
  have hz : (∑' i : ℕ, ν {(f i : X)}) = 0 := by
    have h0 : ∀ i : ℕ, ν {(f i : X)} = 0 := fun i => hd (f i)
    simp [h0]
  rw [hz] at hle
  exact le_antisymm hle zero_le

/-- T_F1'-2 纤维零测件 (叠置域·一般位置): atomless 推映下, 单停点的纤维 (原像) 零测 ——
    随机生成史恰好停在指定停点的概率为零 —— 归宿解释命题钉-1 "纤维测度结构" 真测度版. -/
theorem fiber_null (hπ : Measurable π) (hd : Diffuse (μ.map π)) (x₀ : X) :
    μ (π ⁻¹' {x₀}) = 0 := by
  rw [← MeasureTheory.Measure.map_apply hπ (measurableSet_singleton x₀)]
  exact hd x₀

/-- T_F1'-1 离散读数原子件 (P-a 的定理化): 概率测度经可数值读出映射的推映必有正单点质量
    (读数格 = 原子) —— 离散读数必然产生原子: "一般测度是离散描述" 的严格形式;
    逆否: atomless 推映 (叠置域) 的读出面不可数. -/
theorem discrete_reading_has_atom (hπ : Measurable π) (h1 : μ Set.univ = 1)
    (hcu : (Set.univ : Set X).Countable) :
    ∃ x : X, (μ.map π) {x} ≠ 0 := by
  by_contra hno
  push Not at hno
  obtain ⟨f, hle⟩ := univ_le_tsum_enum (μ.map π) hcu
  have hz : (∑' i : ℕ, (μ.map π) {(f i : X)}) = 0 := by simp [hno]
  rw [hz] at hle
  have h0 : (μ.map π) Set.univ = 0 := le_antisymm hle zero_le
  have h1' : (μ.map π) Set.univ = 1 := by
    rw [MeasureTheory.Measure.map_apply hπ MeasurableSet.univ, Set.preimage_univ, h1]
  rw [h0] at h1'
  exact absurd h1' (by simp)

/-- S-4 叠置需不可数读出面 (P-c 的必然性定理化): 非零测度 + atomless 推映 → 读出值域不可数
    —— 叠置态 (atomless) 只能在不可数读出面 (数轴型连续统) 上成立;
    数轴 = 不可数连续统 = 叠置态的天然实现域 (主人: "叠置态在数轴上成立"). -/
theorem superposition_needs_uncountable (hπ : Measurable π) (hμ0 : μ Set.univ ≠ 0)
    (hd : Diffuse (μ.map π)) : ¬ Countable X := by
  intro hcu
  obtain ⟨f, hle⟩ := univ_le_tsum_enum (μ.map π) (Set.to_countable Set.univ)
  have hz : (∑' i : ℕ, (μ.map π) {(f i : X)}) = 0 := by
    have h0 : ∀ i : ℕ, (μ.map π) {(f i : X)} = 0 := fun i => hd (f i)
    simp [h0]
  rw [hz] at hle
  have h0 : (μ.map π) Set.univ = 0 := le_antisymm hle zero_le
  have h1 : (μ.map π) Set.univ = μ Set.univ := by
    rw [MeasureTheory.Measure.map_apply hπ MeasurableSet.univ, Set.preimage_univ]
  rw [← h1, h0] at hμ0
  exact hμ0 rfl

end Superposition
