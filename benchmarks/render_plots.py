#!/usr/bin/env python3
"""Render publication-grade SVG charts from benchmarks/results/waterfall_results.json.

Outputs:
  - plots/waterfall_ler.svg
  - plots/latency_accuracy_pareto.svg
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
import matplotlib.ticker as ticker
import numpy as np

HERE = Path(__file__).resolve().parent
REPO_ROOT = Path(__file__).resolve().parents[1]


def configure_style() -> None:
    plt.rcParams.update(
        {
            "svg.fonttype": "path",  # Crisp path-rendered glyphs on GitHub light/white backgrounds
            "font.family": "sans-serif",
            "font.sans-serif": ["DejaVu Sans", "Arial", "Helvetica"],
            "font.size": 10.0,
            "axes.titlesize": 11.2,
            "axes.titleweight": "bold",
            "axes.labelsize": 10.2,
            "axes.labelweight": "bold",
            "axes.edgecolor": "#334155",
            "axes.linewidth": 1.05,
            "xtick.color": "#1E293B",
            "ytick.color": "#1E293B",
            "text.color": "#0F172A",
            "figure.facecolor": "#FFFFFF",
            "axes.facecolor": "#FFFFFF",
            "savefig.facecolor": "#FFFFFF",
            "savefig.edgecolor": "#FFFFFF",
            "legend.frameon": True,
            "legend.facecolor": "#FFFFFF",
            "legend.edgecolor": "#CBD5E1",
            "legend.framealpha": 0.97,
        }
    )


def get_circuit_map(data: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {c["key"]: c for c in data["circuits"]}


def extract_curve(
    circ: dict[str, Any], arm_name: str, floor_zero: float | None = None
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    ps, ys, los, his, is_zero = [], [], [], [], []
    for pt in circ["points"]:
        if arm_name not in pt["arms"]:
            continue
        arm = pt["arms"][arm_name]
        errs = int(arm["errors"])
        ler = float(arm["frame_ler"])
        lo = float(arm["wilson95_lo"])
        hi = float(arm["wilson95_hi"])
        if errs == 0:
            if floor_zero is None:
                continue
            ps.append(float(pt["p"]))
            ys.append(floor_zero)
            los.append(floor_zero)
            his.append(max(floor_zero, hi))
            is_zero.append(True)
        else:
            ps.append(float(pt["p"]))
            ys.append(ler)
            los.append(max(1e-6, lo))
            his.append(min(1.0, hi))
            is_zero.append(False)
    return (
        np.array(ps),
        np.array(ys),
        np.array(los),
        np.array(his),
        np.array(is_zero, dtype=bool),
    )


def render_waterfall(data: dict[str, Any], out_path: Path) -> None:
    cmap = get_circuit_map(data)
    stage1 = data.get("stage1_10k_receipts", {})

    fig, (ax_a, ax_b) = plt.subplots(1, 2, figsize=(14.0, 6.9), dpi=150)
    fig.patch.set_facecolor("#FFFFFF")
    fig.subplots_adjust(left=0.068, right=0.985, bottom=0.27, top=0.87, wspace=0.20)

    fig.suptitle(
        "Zero-Idle (4,2) & Non-Abelian 2BGA Co-Design and Drop-In Space-Time Decoding Across Physical Noise Rates",
        fontsize=12.8,
        fontweight="bold",
        color="#0F172A",
        y=0.965,
    )

    for ax in (ax_a, ax_b):
        ax.set_facecolor("#FFFFFF")
        ax.spines["top"].set_visible(False)
        ax.spines["right"].set_visible(False)
        ax.set_xscale("log")
        ax.set_yscale("log")
        ax.grid(True, which="major", color="#E2E8F0", linewidth=0.85, linestyle="-")
        ax.grid(True, which="minor", color="#F1F5F9", linewidth=0.55, linestyle=":")
        ax.set_xlim(4.4e-4, 3.4e-3)
        ax.set_ylim(2.6e-5, 2.8e-1)
        ax.set_xticks([5e-4, 7.5e-4, 1e-3, 1.5e-3, 2e-3, 3e-3])
        ax.get_xaxis().set_major_formatter(
            ticker.FuncFormatter(lambda x, _: f"{x * 100:.3g}%")
        )
        ax.get_xaxis().set_minor_formatter(ticker.NullFormatter())
        ax.set_xlabel("Physical Circuit Error Rate  p  (DEPOLARIZE2 / DEPOLARIZE1 / SPAM)")

    ax_a.set_ylabel("4-Round Logical Frame Error Rate  (P_L)")
    ax_b.set_ylabel("4-Round Logical Frame Error Rate  (P_L)")

    # --- PANEL A: Circuit & Schedule Co-Design ---
    ax_a.set_title(
        "A. Zero-Idle T=6 & Non-Abelian T=7 vs Two-Phase T=12 Baselines",
        pad=10,
        loc="left",
    )

    panel_a_specs = [
        (
            "n60-abelian-t12-collapse",
            "[[60,8,6]] Abelian Z30 Two-Phase T=12 (d_circ=4 collapse)",
            "#DC2626",
            "-.",
            "v",
            False,
            2.1,
            6,
        ),
        (
            "bb84-c1-t12",
            "[[84,8,6]] Canonical (3,3) BB Two-Phase T=12 (d_hook=5)",
            "#0D9488",
            "--",
            "s",
            False,
            1.8,
            5,
        ),
        (
            "n56-t12-twophase",
            "[[56,6,6]] Serialized Two-Phase T=12 (d_hook=5)",
            "#EA580C",
            "--",
            "D",
            False,
            1.8,
            5,
        ),
        (
            "n96-t12-twophase",
            "[[96,8,6]] Serialized Two-Phase T=12 (2× CNOT depth)",
            "#64748B",
            "--",
            "o",
            False,
            1.7,
            4,
        ),
        (
            "n60-nonabelian-t7",
            "[[60,8,6]] Non-Abelian Z5⋊Z6 T=7 (d_circ=6)",
            "#7C3AED",
            "-",
            "^",
            True,
            2.4,
            8,
        ),
        (
            "n56-t6",
            "[[56,6,6]] (4,2) Zero-Idle T=6 (d_circ=6)",
            "#0284C7",
            "-",
            "D",
            True,
            2.3,
            8,
        ),
        (
            "n84-t6",
            "[[84,8,6]] (4,2) Zero-Idle T=6 (d_circ=6)",
            "#059669",
            "-",
            "s",
            True,
            2.5,
            9,
        ),
        (
            "n96-t6",
            "[[96,8,6]] (4,2) Zero-Idle T=6 (d_circ=6)",
            "#1E3A8A",
            "-",
            "o",
            True,
            2.6,
            10,
        ),
    ]

    for key, label, color, ls, marker, filled, lw, z in panel_a_specs:
        if key not in cmap:
            continue
        ps, ys, los, his, _ = extract_curve(cmap[key], "spacetime_batch")
        if len(ps) == 0:
            continue
        mfc = color if filled else "#FFFFFF"
        ax_a.plot(
            ps,
            ys,
            linestyle=ls,
            linewidth=lw,
            color=color,
            marker=marker,
            markersize=6.2,
            markerfacecolor=mfc,
            markeredgecolor=color,
            markeredgewidth=1.6,
            label=label,
            zorder=z,
        )
        yerr_lo = np.maximum(0.0, ys - los)
        yerr_hi = np.maximum(0.0, his - ys)
        ax_a.errorbar(
            ps,
            ys,
            yerr=[yerr_lo, yerr_hi],
            fmt="none",
            ecolor=color,
            elinewidth=0.95,
            capsize=2.2,
            alpha=0.5,
            zorder=z - 1,
        )

    # Clean power-law slope guides in unobstructed space
    p_ref_p2 = np.array([5.4e-4, 1.25e-3])
    y_ref_p2 = 8.5e-2 * (p_ref_p2 / 1.25e-3) ** 2
    ax_a.plot(p_ref_p2, y_ref_p2, color="#991B1B", linestyle=":", linewidth=1.5, zorder=3)
    ax_a.text(
        4.9e-4,
        4.6e-2,
        "O(p²) slope\n(d_circ = 4 hook collapse)",
        fontsize=8.2,
        color="#991B1B",
        fontweight="bold",
    )

    p_ref_p3 = np.array([1.25e-3, 2.85e-3])
    y_ref_p3 = 7.2e-5 * (p_ref_p3 / 1.25e-3) ** 3
    ax_a.plot(p_ref_p3, y_ref_p3, color="#1E3A8A", linestyle=":", linewidth=1.5, zorder=3)
    ax_a.text(
        1.52e-3,
        6.0e-5,
        "O(p³) slope (d_circ = 6)",
        fontsize=8.4,
        color="#1E3A8A",
        fontweight="bold",
    )

    ax_a.legend(
        loc="upper center",
        bbox_to_anchor=(0.48, -0.155),
        ncol=2,
        fontsize=7.6,
        handlelength=2.2,
        columnspacing=1.0,
        borderpad=0.45,
        labelspacing=0.35,
    )

    # --- PANEL B: Drop-in Decoder Comparison on Fixed Circuits (incl. IBM Gross Codes) ---
    ax_b.set_title(
        "B. Drop-In Decoding on Fixed Circuits (incl. IBM Gross)",
        pad=10,
        loc="left",
    )

    panel_b_families = [
        ("ibm72-published-r4", "IBM [[72,12,6]] Gross (r=4)", "#0284C7", "o", "ibm72-published-r4"),
        ("n70-t10-r4", "[[70,6,8]] 2BGA T=10 (d_circ=7)", "#D97706", "D", "n70-r4"),
        ("n60-nonabelian-t7", "[[60,8,6]] Non-Abelian T=7", "#7C3AED", "^", "n60-nonabelian-r4"),
        ("n84-t6", "[[84,8,6]] Zero-Idle T=6", "#059669", "s", "n84-r4"),
        ("ibm144-published-r4", "IBM [[144,12,12]] Gross (r=4)", "#0F766E", "P", "ibm144-published-r4"),
    ]

    family_handles = []
    for key, fam_label, color, marker, s1_stem_prefix in panel_b_families:
        if key not in cmap:
            continue
        circ = cmap[key]

        ps_r, ys_r, _, _, _ = extract_curve(circ, "cpp_bposd_cs2")
        if len(ps_r) > 0:
            ax_b.plot(
                ps_r,
                ys_r,
                linestyle="--",
                linewidth=1.75,
                color=color,
                marker=marker,
                markersize=5.6,
                markerfacecolor="#FFFFFF",
                markeredgecolor=color,
                markeredgewidth=1.4,
                alpha=0.88,
                zorder=5,
            )

        ps_s, ys_s, los_s, his_s, _ = extract_curve(circ, "spacetime_batch")
        if len(ps_s) > 0:
            ax_b.plot(
                ps_s,
                ys_s,
                linestyle="-",
                linewidth=2.4,
                color=color,
                marker=marker,
                markersize=6.4,
                markerfacecolor=color,
                markeredgecolor=color,
                zorder=8,
            )
            ax_b.errorbar(
                ps_s,
                ys_s,
                yerr=[np.maximum(0.0, ys_s - los_s), np.maximum(0.0, his_s - ys_s)],
                fmt="none",
                ecolor=color,
                elinewidth=0.9,
                capsize=2.0,
                alpha=0.5,
                zorder=7,
            )

        ldpc_p, ldpc_y = [], []
        for pt in circ["points"]:
            p_val = float(pt["p"])
            s1_key = f"{s1_stem_prefix}-p{p_val:.3f}"
            if p_val in (0.001, 0.002) and s1_key in stage1 and "ldpc2" in stage1[s1_key]:
                rec = stage1[s1_key]["ldpc2"]
                if int(rec["errors"]) > 0:
                    ldpc_p.append(p_val)
                    ldpc_y.append(float(rec["frame_ler"]))
                    continue
            if "ldpc_bposd_cs2_anchor" in pt["arms"]:
                anc = pt["arms"]["ldpc_bposd_cs2_anchor"]
                if int(anc["errors"]) > 0:
                    ldpc_p.append(p_val)
                    ldpc_y.append(float(anc["frame_ler"]))
        if ldpc_p:
            ax_b.scatter(
                ldpc_p,
                ldpc_y,
                marker="*",
                s=105,
                facecolor="#FFFFFF",
                edgecolor=color,
                linewidths=1.6,
                zorder=9,
            )

        family_handles.append(
            Line2D(
                [0],
                [0],
                color=color,
                marker=marker,
                markersize=6.2,
                linewidth=2.3,
                label=fam_label,
            )
        )

    # Upper-bound marker at p=0.2% for IBM [[144,12,12]] (0 / 10,000 errors) + dashed link to p=0.3%
    ax_b.plot([2.0e-3, 3.0e-3], [5.5e-5, 4.0e-4], color="#0F766E", linestyle=":", linewidth=1.5, zorder=7)
    ax_b.scatter(
        [2.0e-3],
        [5.5e-5],
        marker="v",
        s=85,
        facecolor="#FFFFFF",
        edgecolor="#0F766E",
        linewidths=1.8,
        zorder=10,
    )
    ax_b.annotate(
        "IBM [[144,12,12]] Gross:\n0 / 10,000 errors at p ≤ 0.2%\n(d_circ = 10, 2/5k at 0.3%)",
        xy=(2.0e-3, 5.5e-5),
        xytext=(4.75e-4, 3.6e-5),
        fontsize=7.7,
        fontweight="bold",
        color="#0F766E",
        bbox=dict(boxstyle="round,pad=0.28", fc="#F0FDFA", ec="#0F766E", lw=0.95),
        arrowprops=dict(arrowstyle="->", color="#0F766E", lw=1.2),
        zorder=11,
    )

    decoder_style_handles = [
        Line2D([0], [0], color="#1E293B", lw=2.4, ls="-", marker="o", mfc="#1E293B", ms=5.8, label="SpaceTimeDecoder (13–177 µs)"),
        Line2D([0], [0], color="#1E293B", lw=1.7, ls="--", marker="o", mfc="#FFFFFF", ms=5.5, label="C++17 BP+OSD-CS (0.8–8.8 ms)"),
        Line2D([0], [0], color="#1E293B", lw=0.0, marker="*", mfc="#FFFFFF", ms=9.0, mew=1.5, label="ldpc.BpOsdDecoder OSD-CS (42–1,438 ms)"),
    ]

    leg_dec = ax_b.legend(
        handles=decoder_style_handles,
        loc="upper left",
        fontsize=7.8,
        title="Decoder Arm (byte-identical syndromes)",
        title_fontsize=8.0,
        borderpad=0.45,
    )
    ax_b.add_artist(leg_dec)
    ax_b.legend(
        handles=family_handles,
        loc="upper center",
        bbox_to_anchor=(0.50, -0.155),
        ncol=2,
        fontsize=7.7,
        columnspacing=1.1,
        borderpad=0.45,
        labelspacing=0.35,
    )

    out_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_path, format="svg")
    plt.close(fig)
    print(f"Rendered {out_path} ({out_path.stat().st_size} bytes)")


def render_pareto(data: dict[str, Any], out_path: Path) -> None:
    cmap = get_circuit_map(data)
    stage1 = data.get("stage1_10k_receipts", {})

    fig, ax = plt.subplots(figsize=(11.4, 6.8), dpi=150)
    fig.patch.set_facecolor("#FFFFFF")
    ax.set_facecolor("#FFFFFF")
    fig.subplots_adjust(left=0.09, right=0.975, bottom=0.12, top=0.87)

    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlim(7.5, 1.6e6)
    ax.set_ylim(3.4e-5, 9.5e-2)
    ax.grid(True, which="major", color="#E2E8F0", linewidth=0.85, linestyle="-")
    ax.grid(True, which="minor", color="#F1F5F9", linewidth=0.55, linestyle=":")

    # Shaded reference budget regions (assumed thresholds, not measured timing contracts)
    ax.axvspan(7.5, 250.0, color="#ECFDF5", alpha=0.62, zorder=1)
    ax.axvline(250.0, color="#059669", linestyle="--", linewidth=1.6, zorder=4)
    ax.text(
        230.0,
        7.4e-2,
        "Assumed superconducting budget\n(≤ 250 µs / shot; mean CPU time shown)",
        ha="right",
        va="top",
        fontsize=8.6,
        fontweight="bold",
        color="#065F46",
        bbox=dict(boxstyle="round,pad=0.28", fc="#FFFFFF", ec="#6EE7B7", alpha=0.95),
        zorder=10,
    )

    ax.axvline(1000.0, color="#D97706", linestyle="--", linewidth=1.5, zorder=4)
    ax.text(
        1100.0,
        7.4e-2,
        "Assumed neutral-atom / modular budget\n(≤ 1,000 µs / shot)",
        ha="left",
        va="top",
        fontsize=8.6,
        fontweight="bold",
        color="#92400E",
        bbox=dict(boxstyle="round,pad=0.28", fc="#FFFFFF", ec="#FCD34D", alpha=0.95),
        zorder=10,
    )

    # Hand-tuned per-point label offsets: (st_offset, st_ha), (ref_offset, ref_ha), (ldpc_offset, ldpc_ha)
    pareto_items = [
        (
            "n56-t6",
            "n56-r4-p0.002",
            "[[56,6,6]]@T=6",
            ((-8, 6), "right"),
            ((-8, 5), "right"),
            ((-8, 5), "right"),
        ),
        (
            "n60-nonabelian-t7",
            "n60-nonabelian-r4-p0.002",
            "[[60,8,6]]@T=7",
            ((8, 7), "left"),
            ((8, 4), "left"),
            ((-8, -11), "right"),
        ),
        (
            "n84-t6",
            "n84-r4-p0.002",
            "[[84,8,6]]@T=6",
            ((-9, -12), "right"),
            ((8, -10), "left"),
            ((8, -10), "left"),
        ),
        (
            "n96-t6",
            "n96-r4-p0.002",
            "[[96,8,6]]@T=6",
            ((9, 4), "left"),
            ((8, 4), "left"),
            ((8, 4), "left"),
        ),
        (
            "n70-t10-r4",
            "n70-r4-p0.002",
            "[[70,6,8]]@T=10",
            ((9, -3), "left"),
            ((9, -3), "left"),
            ((8, 4), "left"),
        ),
        (
            "ibm72-published-r4",
            "ibm72-published-r4-p0.002",
            "IBM [[72,12,6]]",
            ((10, -4), "left"),
            ((8, 5), "left"),
            ((8, 5), "left"),
        ),
        (
            "ibm144-published-r4",
            "ibm144-published-r4-p0.002",
            "IBM [[144,12,12]]",
            ((9, 6), "left"),
            ((9, 6), "left"),
            ((-8, 8), "right"),
        ),
    ]

    ZERO_FLOOR_Y = 5.2e-5

    for w_key, s1_key, short_label, (st_off, st_ha), (ref_off, ref_ha), (ld_off, ld_ha) in pareto_items:
        pt_002 = next(
            (pt for pt in cmap[w_key]["points"] if abs(pt["p"] - 0.002) < 1e-12),
            None,
        )
        s1 = stage1.get(s1_key, {})

        if "scalar" in s1 and "reference" in s1:
            st_us = float(s1["scalar"]["us_per_shot"])
            st_ler = float(s1["scalar"]["frame_ler"])
            st_zero = int(s1["scalar"]["errors"]) == 0
            ref_us = float(s1["reference"]["us_per_shot"])
            ref_ler = float(s1["reference"]["frame_ler"])
            ref_zero = int(s1["reference"]["errors"]) == 0
        elif pt_002 is not None:
            st_arm = pt_002["arms"].get("spacetime_scalar", pt_002["arms"]["spacetime_batch"])
            st_us = float(st_arm["us_per_shot"])
            st_ler = float(st_arm["frame_ler"])
            st_zero = int(st_arm["errors"]) == 0
            ref_arm = pt_002["arms"]["cpp_bposd_cs2"]
            ref_us = float(ref_arm["us_per_shot"])
            ref_ler = float(ref_arm["frame_ler"])
            ref_zero = int(ref_arm["errors"]) == 0
        else:
            continue

        ldpc_us, ldpc_ler, ldpc_zero = None, None, False
        if "ldpc2" in s1:
            ldpc_us = float(s1["ldpc2"]["us_per_shot"])
            ldpc_ler = float(s1["ldpc2"]["frame_ler"])
            ldpc_zero = int(s1["ldpc2"]["errors"]) == 0
        elif pt_002 is not None and "ldpc_bposd_cs2_anchor" in pt_002["arms"]:
            anc = pt_002["arms"]["ldpc_bposd_cs2_anchor"]
            ldpc_us = float(anc["us_per_shot"])
            ldpc_ler = float(anc["frame_ler"])
            ldpc_zero = int(anc["errors"]) == 0

        y_st_plot = ZERO_FLOOR_Y if st_zero else st_ler
        y_ref_plot = ZERO_FLOOR_Y if ref_zero else ref_ler

        if ldpc_us is not None and ldpc_ler is not None:
            y_ldpc_plot = ZERO_FLOOR_Y if ldpc_zero else ldpc_ler
            ax.plot(
                [ldpc_us, ref_us, st_us],
                [y_ldpc_plot, y_ref_plot, y_st_plot],
                color="#CBD5E1",
                linestyle="-",
                linewidth=1.1,
                zorder=2,
            )
            ax.scatter(
                [ldpc_us],
                [y_ldpc_plot],
                marker="v" if ldpc_zero else "s",
                s=78,
                facecolor="#FFFFFF" if ldpc_zero else "#DC2626",
                edgecolor="#DC2626",
                linewidths=1.6,
                zorder=6,
            )
            ax.annotate(
                short_label,
                xy=(ldpc_us, y_ldpc_plot),
                xytext=ld_off,
                textcoords="offset points",
                ha=ld_ha,
                fontsize=7.5,
                color="#991B1B",
                zorder=7,
            )
        else:
            ax.plot(
                [ref_us, st_us],
                [y_ref_plot, y_st_plot],
                color="#CBD5E1",
                linestyle="-",
                linewidth=1.1,
                zorder=2,
            )

        ax.scatter(
            [ref_us],
            [y_ref_plot],
            marker="v" if ref_zero else "^",
            s=82,
            facecolor="#FFFFFF" if ref_zero else "#EA580C",
            edgecolor="#EA580C",
            linewidths=1.6,
            zorder=7,
        )
        ax.annotate(
            short_label,
            xy=(ref_us, y_ref_plot),
            xytext=ref_off,
            textcoords="offset points",
            ha=ref_ha,
            fontsize=7.5,
            color="#9A3412",
            zorder=7,
        )

        ax.scatter(
            [st_us],
            [y_st_plot],
            marker="v" if st_zero else "o",
            s=105,
            facecolor="#FFFFFF" if st_zero else "#0284C7",
            edgecolor="#0369A1",
            linewidths=2.0,
            zorder=9,
        )
        lbl_txt = (
            f"{short_label} (0/10k err, {st_us:.0f} µs)"
            if st_zero
            else f"{short_label} ({st_us:.0f} µs)"
        )
        ax.annotate(
            lbl_txt,
            xy=(st_us, y_st_plot),
            xytext=st_off,
            textcoords="offset points",
            ha=st_ha,
            fontsize=8.0,
            fontweight="bold",
            color="#0C4A6E",
            zorder=10,
        )

    # Callout highlighting Pareto sweet spot
    ax.annotate(
        "SpaceTimeDecoder Pareto Sweet Spot:\n• 16×–41× faster & 2.8×–15× fewer errors than C++17 BP+OSD-CS\n• 2,070×–4,210× faster than Python/Cython ldpc.BpOsdDecoder",
        xy=(65.8, 7.0e-4),
        xytext=(580.0, 1.35e-4),
        fontsize=8.3,
        fontweight="bold",
        color="#0F172A",
        bbox=dict(boxstyle="round,pad=0.38", fc="#F8FAFC", ec="#0284C7", lw=1.2),
        arrowprops=dict(
            arrowstyle="->",
            connectionstyle="arc3,rad=-0.16",
            color="#0284C7",
            lw=1.5,
        ),
        zorder=11,
    )

    # Place legend cleanly in the empty upper-right band below the budget banners
    legend_handles = [
        Line2D(
            [0],
            [0],
            marker="o",
            color="none",
            markerfacecolor="#0284C7",
            markeredgecolor="#0369A1",
            markeredgewidth=1.8,
            markersize=8.2,
            label="SpaceTimeDecoder (N=1 scalar, 0 heap allocs: 43–177 µs)",
        ),
        Line2D(
            [0],
            [0],
            marker="^",
            color="none",
            markerfacecolor="#EA580C",
            markeredgecolor="#EA580C",
            markersize=8.0,
            label="C++17 Reference BP+OSD-CS (order 2, K=20: 1,176–7,100 µs)",
        ),
        Line2D(
            [0],
            [0],
            marker="s",
            color="none",
            markerfacecolor="#DC2626",
            markeredgecolor="#DC2626",
            markersize=7.8,
            label="Open-Source ldpc.BpOsdDecoder (OSD-CS: 88,400–634,700 µs)",
        ),
        Line2D(
            [0],
            [0],
            marker="v",
            color="none",
            markerfacecolor="#FFFFFF",
            markeredgecolor="#334155",
            markeredgewidth=1.6,
            markersize=8.0,
            label="Open downward triangle: 0 / 10,000 errors (< 10⁻⁴ upper bound)",
        ),
    ]
    ax.legend(
        handles=legend_handles,
        loc="upper right",
        bbox_to_anchor=(0.99, 0.80),
        fontsize=8.0,
        borderpad=0.5,
        labelspacing=0.38,
    )

    ax.set_title(
        "Single-Shot Decode Latency vs Logical Error Rate at p = 0.002 (4-Round Z-Memory Circuits)",
        fontsize=12.0,
        fontweight="bold",
        pad=12,
    )
    ax.set_xlabel("Mean Single-Shot Decode CPU Time  (total CPU s ÷ shots, µs / shot, log scale)")
    ax.set_ylabel("4-Round Logical Frame Error Rate at p = 0.002  (log scale)")
    ax.xaxis.set_major_formatter(
        ticker.FuncFormatter(lambda x, _: f"{int(x):,}" if x >= 1 else f"{x:g}")
    )

    out_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_path, format="svg")
    plt.close(fig)
    print(f"Rendered {out_path} ({out_path.stat().st_size} bytes)")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--input",
        type=Path,
        default=HERE / "results" / "waterfall_results.json",
        help="Input waterfall_results.json path",
    )
    parser.add_argument(
        "--plots-dir",
        "--out-dir",
        dest="plots_dir",
        type=Path,
        default=REPO_ROOT / "plots",
        help="Output plots directory",
    )
    args = parser.parse_args()

    configure_style()
    data = json.loads(args.input.read_text())
    render_waterfall(data, args.plots_dir / "waterfall_ler.svg")
    render_pareto(data, args.plots_dir / "latency_accuracy_pareto.svg")


if __name__ == "__main__":
    main()
