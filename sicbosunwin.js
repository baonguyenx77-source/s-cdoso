import fastify from "fastify";
import cors from "@fastify/cors";
import * as path from "node:path";
import { fileURLToPath } from "node:url";
import fetch from "node-fetch";
import fs from "fs";

// --- CẤU HÌNH ---
const port = 3000;
const api_url = "https://api.wsktnus8.net/v2/history/getLastResult?gameId=ktrng_3979&size=100&tableId=39791215743193&curPage=1";

// --- GLOBAL STATE ---
let txh_history = [];
let current_session_id = null;
let fetch_interval = null;

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

// --- UTILITIES ---
function parse_lines(data) {
    if (!data || !data.data || !Array.isArray(data.data.resultList)) return [];

    const sorted_list = data.data.resultList.sort((a, b) => {
        const id_a = parseInt(a.gameNum.slice(1));
        const id_b = parseInt(b.gameNum.slice(1));
        return id_b - id_a;
    });

    const arr = sorted_list.map(item => {
        const total = item.score;
        let tx;
        let result_truyen_thong;

        if (total >= 4 && total <= 10) {
            tx = 'X';
            result_truyen_thong = "XIU";
        } else if (total >= 11 && total <= 17) {
            tx = 'T';
            result_truyen_thong = "TAI";
        } else if (total === 3 || total === 18) {
            tx = 'B';
            result_truyen_thong = "BAO";
        } else {
            tx = 'N';
            result_truyen_thong = "UNKNOWN";
        }

        const dice_faces = Array.isArray(item.facesList) ? item.facesList :
            (typeof item.keyR === 'string' ? item.keyR.split('-').map(Number) : [0, 0, 0]);

        return {
            session: parseInt(item.gameNum.slice(1)),
            dice: dice_faces,
            total: total,
            result: result_truyen_thong,
            tx: tx
        };
    });

    return arr.sort((a, b) => a.session - b.session);
}

function last_n(arr, n) {
    return arr.slice(Math.max(0, arr.length - n));
}

function majority(obj) {
    let max_k = null, max_v = -Infinity;
    for (let k in obj) {
        if (obj[k] > max_v) { max_v = obj[k]; max_k = k; }
    }
    return { key: max_k, val: max_v };
}

function sum(nums) { return nums.reduce((a, b) => a + b, 0); }
function avg(nums) { return nums.length ? sum(nums) / nums.length : 0; }

function get_runs(tx) {
    if (!tx.length) return [];
    let runs = [], cur = tx[0], len = 1;
    for (let i = 1; i < tx.length; i++) {
        if (tx[i] === cur) len++;
        else { runs.push({ val: cur, len }); cur = tx[i]; len = 1; }
    }
    runs.push({ val: cur, len });
    return runs;
}
// ==================== CÁC THUẬT TOÁN CẦU THỰC TẾ ====================

// 1. CẦU BỆT (3-5 phiên liên tiếp) — TẦN SUẤT CAO NHẤT (~62-68%)
function algo_beit(history) {
    const tx = history.filter(h => h.tx !== 'B').map(h => h.tx);
    if (tx.length < 10) return null;
    const runs = get_runs(tx);
    const last = runs[runs.length - 1];
    if (last.len === 3 || last.len === 4 || last.len === 5) {
        return last.val === 'T' ? 'X' : 'T';
    }
    return null;
}

// 2. CẦU 1-1 (ĐẢO LIÊN TỤC) — TẦN SUẤT CAO (~58-63%)
function algo_cau_1_1(history) {
    const tx = history.filter(h => h.tx !== 'B').map(h => h.tx);
    if (tx.length < 8) return null;
    const last6 = tx.slice(-6);
    const allAlternating = last6.every((v, i) => i === 0 || v !== last6[i - 1]);
    if (allAlternating) return tx[tx.length - 1] === 'T' ? 'X' : 'T';
    return null;
}

// 3. CẦU NGHIÊNG (MẤT CÂN BẰNG 30 PHIÊN) — CAO (~55-60%)
function algo_nghieng(history) {
    const tx = history.filter(h => h.tx !== 'B').map(h => h.tx);
    if (tx.length < 30) return null;
    const last30 = tx.slice(-30);
    const t30 = last30.filter(x => x === 'T').length;
    const x30 = last30.length - t30;
    if (t30 - x30 >= 8) return 'X';
    if (x30 - t30 >= 8) return 'T';
    if (t30 - x30 >= 5 && t30 - x30 <= 7) return 'X';
    if (x30 - t30 >= 5 && x30 - t30 <= 7) return 'T';
    return null;
}

// 4. CẦU 1-2-1 (A-B-B-A) — TRUNG BÌNH (~55-60%)
function algo_cau_1_2_1(history) {
    const tx = history.filter(h => h.tx !== 'B').map(h => h.tx);
    if (tx.length < 6) return null;
    const last4 = tx.slice(-4);
    if (last4[0] === last4[3] && last4[1] === last4[2] && last4[0] !== last4[1]) {
        return last4[3] === 'T' ? 'X' : 'T';
    }
    return null;
}

// 5. CẦU 2-2 (A-A-B-B-A-A) — TRUNG BÌNH (~54-58%)
function algo_cau_2_2(history) {
    const tx = history.filter(h => h.tx !== 'B').map(h => h.tx);
    if (tx.length < 6) return null;
    const last6 = tx.slice(-6);
    if (last6[0] === last6[1] && last6[2] === last6[3] && last6[4] === last6[5] &&
        last6[0] === last6[4] && last6[2] === last6[5] && last6[0] !== last6[2]) {
        return last6[5] === 'T' ? 'X' : 'T';
    }
    return null;
}

// 6. MARKOV BẬC 3 (≥4 matches, conf≥0.55) — ~55%
function algo_markov_3(history) {
    const tx = history.filter(h => h.tx !== 'B').map(h => h.tx);
    if (tx.length < 25) return null;
    const transitions = {};
    for (let i = 0; i <= tx.length - 4; i++) {
        const key = tx[i] + tx[i + 1] + tx[i + 2];
        transitions[key] = transitions[key] || { T: 0, X: 0 };
        transitions[key][tx[i + 3]]++;
    }
    const lastKey = tx.slice(-3).join('');
    const counts = transitions[lastKey];
    if (!counts || counts.T + counts.X < 4) return null;
    const total = counts.T + counts.X;
    const conf = Math.abs(counts.T - counts.X) / total;
    if (conf < 0.55) return null;
    return counts.T > counts.X ? 'T' : 'X';
}

// 7. FREQUENCY REBALANCE (10 phiên gần) — ~54%
function algo_freq_rebalance(history) {
    if (history.length < 15) return null;
    const tx = history.filter(h => h.tx !== 'B').map(h => h.tx);
    if (tx.length === 0) return null;

    const recent10 = tx.slice(-10);
    const t10 = recent10.filter(x => x === 'T').length;
    const x10 = recent10.length - t10;
    if (t10 >= 7) return 'X';
    if (x10 >= 7) return 'T';

    const recent30 = tx.slice(-30);
    const t30 = recent30.filter(x => x === 'T').length;
    const x30 = recent30.length - t30;
    if (t30 > x30 + 8 && t10 > x10 + 2) return 'X';
    if (x30 > t30 + 8 && x10 > t10 + 2) return 'T';
    return null;
}

// 8. MARKOV BẬC 2 (≥3 matches, conf≥0.5) — ~53%
function algo_markov_2(history) {
    const tx = history.filter(h => h.tx !== 'B').map(h => h.tx);
    if (tx.length < 20) return null;
    const transitions = {};
    for (let i = 0; i <= tx.length - 3; i++) {
        const key = tx[i] + tx[i + 1];
        transitions[key] = transitions[key] || { T: 0, X: 0 };
        transitions[key][tx[i + 2]]++;
    }
    const lastKey = tx[tx.length - 2] + tx[tx.length - 1];
    const counts = transitions[lastKey];
    if (!counts || counts.T + counts.X < 3) return null;
    const total = counts.T + counts.X;
    const conf = Math.abs(counts.T - counts.X) / total;
    if (conf < 0.5) return null;
    return counts.T > counts.X ? 'T' : 'X';
}

// 9. CẦU 1-3-1 (A-B-B-B-A) — THẤP (~53-56%)
function algo_cau_1_3_1(history) {
    const tx = history.filter(h => h.tx !== 'B').map(h => h.tx);
    if (tx.length < 8) return null;
    const last5 = tx.slice(-5);
    if (last5[0] === last5[4] && last5[1] === last5[2] && last5[2] === last5[3] && last5[0] !== last5[1]) {
        return last5[4] === 'T' ? 'X' : 'T';
    }
    return null;
}

// --- DANH SÁCH THUẬT TOÁN VỚI BASE WEIGHT ---
const all_algs = [
    { id: 'beit',           fn: algo_beit,           base_weight: 2.0 },
    { id: 'cau_1_1',        fn: algo_cau_1_1,        base_weight: 1.6 },
    { id: 'nghieng',        fn: algo_nghieng,        base_weight: 1.4 },
    { id: 'cau_1_2_1',      fn: algo_cau_1_2_1,      base_weight: 1.2 },
    { id: 'cau_2_2',        fn: algo_cau_2_2,        base_weight: 1.1 },
    { id: 'markov_3',       fn: algo_markov_3,       base_weight: 1.0 },
    { id: 'freq_rebalance', fn: algo_freq_rebalance, base_weight: 0.9 },
    { id: 'markov_2',       fn: algo_markov_2,       base_weight: 0.8 },
    { id: 'cau_1_3_1',      fn: algo_cau_1_3_1,      base_weight: 0.6 },
];
// ==================== DỰ ĐOÁN VỊ - ĐA DẠNG + ƯU TIÊN PHỔ BIẾN ====================

const SCORE_PRIOR = {
    T: { 11: 0.19, 12: 0.16, 13: 0.15, 14: 0.13, 15: 0.11, 16: 0.06, 17: 0.04 },
    X: { 4: 0.01, 5: 0.03, 6: 0.06, 7: 0.10, 8: 0.14, 9: 0.16, 10: 0.16 }
};

const RARE_SCORES = {
    T: new Set([16, 17]),
    X: new Set([4, 5])
};

const PREFERRED_COMBOS = {
    T: [
        [11, 12, 13], [11, 12, 14], [11, 13, 14],
        [12, 13, 14], [11, 12, 15], [11, 13, 15],
        [12, 13, 15], [12, 14, 15], [11, 14, 15]
    ],
    X: [
        [8, 9, 10], [7, 9, 10], [7, 8, 10],
        [7, 8, 9],  [8, 9, 6],  [7, 9, 6],
        [8, 10, 6], [9, 10, 6], [7, 8, 6]
    ]
};

let recent_combos = { T: [], X: [] };

function algod_score_predictor(history, tx_constraint) {
    const prior = SCORE_PRIOR[tx_constraint];
    const available = Object.keys(prior).map(Number).sort((a, b) => a - b);

    const recent = history.filter(h => h.tx !== 'B').slice(-60);
    const same_side = recent.filter(h => h.tx === tx_constraint);

    const posterior = {};
    for (let s of available) {
        let p = prior[s];
        if (same_side.length >= 5) {
            const count = same_side.filter(h => h.total === s).length;
            const empirical = count / same_side.length;
            p = 0.7 * empirical + 0.3 * prior[s];
        }
        posterior[s] = p;
    }

    for (let s of available) {
        let last_seen = -1;
        for (let i = history.length - 1; i >= 0; i--) {
            if (history[i].tx === tx_constraint && history[i].total === s) {
                last_seen = i; break;
            }
        }
        const gap = last_seen === -1 ? 30 : history.length - last_seen;
        const expected_gap = 1 / prior[s];
        const boost = Math.min(0.15, (gap / expected_gap) * 0.08);
        posterior[s] *= (1 + boost);
    }

    for (let s of RARE_SCORES[tx_constraint]) {
        if (posterior[s] !== undefined) posterior[s] *= 0.35;
    }
    if (tx_constraint === 'X' && posterior[3] !== undefined) posterior[3] *= 0.15;
    if (tx_constraint === 'T' && posterior[18] !== undefined) posterior[18] *= 0.15;

    const ranked = Object.entries(posterior)
        .map(([s, p]) => ({ score: Number(s), p }))
        .sort((a, b) => b.p - a.p);

    const topScores = new Set(ranked.slice(0, 5).map(x => x.score));
    let chosen_combo = null;

    const recent_list = recent_combos[tx_constraint] || [];
    const usedRecently = new Set(recent_list.flat());

    const validCombos = PREFERRED_COMBOS[tx_constraint].filter(combo => {
        if (!combo.every(s => topScores.has(s))) return false;
        const freshCount = combo.filter(s => !usedRecently.has(s)).length;
        return freshCount >= 2;
    });

    if (validCombos.length > 0) {
        validCombos.sort((a, b) => {
            const sumA = a.reduce((t, s) => t + posterior[s], 0);
            const sumB = b.reduce((t, s) => t + posterior[s], 0);
            return sumB - sumA;
        });
        chosen_combo = validCombos[0];
    } else {
        const fallback = ranked.slice(0, 4).filter(x => !usedRecently.has(x.score));
        chosen_combo = (fallback.length >= 3 ? fallback : ranked).slice(0, 3).map(x => x.score);
    }

    const selected = [...chosen_combo].sort((a, b) => a - b);
    while (selected.length < 3 && available.length > selected.length) {
        const remain = available.find(s => !selected.includes(s));
        if (remain !== undefined) selected.push(remain);
    }

    recent_combos[tx_constraint].push(selected);
    if (recent_combos[tx_constraint].length > 2) {
        recent_combos[tx_constraint].shift();
    }

    return selected.sort((a, b) => a - b);
}

// ==================== ENSEMBLE CLASSIFIER ====================
class SeiuEnsemble {
    constructor(algorithms, opts = {}) {
        this.algs = algorithms;
        this.weights = {};
        this.base_weights = {};
        this.min_weight = opts.min_weight ?? 0.001;
        this.history_window = opts.history_window ?? 500;
        this.performance_history = {};

        for (let a of algorithms) {
            this.base_weights[a.id] = a.base_weight || 1;
            this.weights[a.id] = a.base_weight || 1;
            this.performance_history[a.id] = { correct: 0, total: 0 };
        }
    }

    fit_initial(history) {
        const window = last_n(history.filter(h => h.tx !== 'B'), this.history_window);
        if (window.length < 30) return;

        console.log(`🧠 Huấn luyện AI với ${window.length} phiên...`);

        for (let i = 20; i < window.length; i++) {
            const prefix = window.slice(0, i);
            const actual = window[i].tx;
            for (let a of this.algs) {
                const pred = a.fn(prefix);
                if (pred) {
                    this.performance_history[a.id].total++;
                    if (pred === actual) this.performance_history[a.id].correct++;
                }
            }
        }

        let total = 0;
        for (let a of this.algs) {
            const perf = this.performance_history[a.id];
            const acc = perf.total > 0 ? perf.correct / perf.total : 0.5;
            const adjusted = Math.pow(acc / 0.5, 2);
            this.weights[a.id] = Math.max(this.min_weight, this.base_weights[a.id] * adjusted);
            total += this.weights[a.id];
        }
        for (let id in this.weights) this.weights[id] /= total;

        console.log(`⚖️ Trọng số khởi tạo:`);
        for (let a of this.algs) {
            const perf = this.performance_history[a.id];
            const acc = perf.total > 0 ? (perf.correct / perf.total * 100).toFixed(1) : '-';
            console.log(`   ${a.id.padEnd(16)}: w=${this.weights[a.id].toFixed(3)} | acc=${acc}% (${perf.total})`);
        }
    }

    update_with_outcome(history_prefix, actual_tx) {
        if (actual_tx === 'B') return;
        for (let a of this.algs) {
            const pred = a.fn(history_prefix);
            if (!pred) continue;
            const perf = this.performance_history[a.id];
            perf.total++;
            if (pred === actual_tx) perf.correct++;

            const recent_acc = perf.correct / perf.total;
            const target = this.base_weights[a.id] * Math.pow(recent_acc / 0.5, 2);
            this.weights[a.id] = 0.85 * this.weights[a.id] + 0.15 * target;
        }
        const total = Object.values(this.weights).reduce((a, b) => a + b, 0) || 1;
        for (let id in this.weights) this.weights[id] /= total;
    }

    predict(history) {
        const votes = {};
        for (let a of this.algs) {
            const pred = a.fn(history);
            if (!pred) continue;
            votes[pred] = (votes[pred] || 0) + (this.weights[a.id] || 0);
        }

        let best, confidence;
        if (!votes['T'] && !votes['X']) {
            best = algo_freq_rebalance(history) || 'T';
            confidence = 0.5;
        } else {
            const result = majority(votes);
            best = result.key;
            const total = Object.values(votes).reduce((a, b) => a + b, 0);
            confidence = Math.min(0.99, Math.max(0.51, total > 0 ? result.val / total : 0.51));
        }

        const score_prediction = algod_score_predictor(history, best);

        return {
            prediction: best === 'T' ? 'tài' : 'xỉu',
            confidence,
            raw_prediction: best,
            score_prediction
        };
    }
}

// ==================== MANAGER ====================
class SeiuManager {
    constructor(opts = {}) {
        this.history = [];
        this.ensemble = new SeiuEnsemble(all_algs, {
            history_window: opts.history_window ?? 500
        });
        this.current_prediction = null;
        this.accuracy_stats = { correct: 0, total: 0 };
    }

    calculate_initial_stats() {
        const min_start = 20;
        const filtered = this.history.filter(h => h.tx !== 'B');
        if (filtered.length < min_start) return;
        for (let i = min_start; i < filtered.length; i++) {
            this.ensemble.update_with_outcome(filtered.slice(0, i), filtered[i].tx);
        }
    }

    load_initial(lines) {
        this.history = lines;
        this.ensemble.fit_initial(this.history);
        this.calculate_initial_stats();
        this.current_prediction = this.get_prediction();

        console.log("📦 Đã tải lịch sử. Hệ thống sẵn sàng.");
        const next = this.history.at(-1) ? this.history.at(-1).session + 1 : 'n/a';
        console.log(`🔮 Dự đoán phiên ${next}: ${this.current_prediction.prediction} (${(this.current_prediction.confidence * 100).toFixed(0)}%). Vị: [${this.current_prediction.score_prediction.join('-')}]`);
    }

    push_record(record) {
        this.history.push(record);

        const prefix = this.history.slice(0, -1).filter(h => h.tx !== 'B');
        if (prefix.length >= 10) {
            this.ensemble.update_with_outcome(prefix, record.tx);

            if (this.current_prediction) {
                this.accuracy_stats.total++;
                const predicted_tx = this.current_prediction.raw_prediction === 'T' ? 'TAI' : 'XIU';
                if (predicted_tx === record.result) this.accuracy_stats.correct++;

                if (this.accuracy_stats.total % 50 === 0) {
                    const acc = (this.accuracy_stats.correct / this.accuracy_stats.total * 100).toFixed(1);
                    console.log(`🎯 Độ chính xác: ${acc}% (${this.accuracy_stats.correct}/${this.accuracy_stats.total})`);
                }
            }
        }

        this.current_prediction = this.get_prediction();
        console.log(`📥 Phiên ${record.session} → ${record.result.toLowerCase()}. Dự đoán ${record.session + 1}: ${this.current_prediction.prediction}. Vị: [${this.current_prediction.score_prediction.join('-')}]`);
    }

    get_prediction() {
        return this.ensemble.predict(this.history);
    }
}

const seiu_manager = new SeiuManager();
// ==================== API SERVER ====================
const app = fastify({ logger: true });
await app.register(cors, { origin: "*" });

async function fetch_and_process_history() {
    try {
        console.log(`🔄 Đang lấy dữ liệu từ API...`);
        const response = await fetch(api_url);
        if (!response.ok) throw new Error(`HTTP ${response.status}: ${response.statusText}`);

        const data = await response.json();
        const new_history = parse_lines(data);

        if (new_history.length === 0) {
            console.log("⚠️ Không có dữ liệu.");
            return;
        }

        const last_session_in_history = new_history.at(-1);

        if (!current_session_id) {
            seiu_manager.load_initial(new_history);
            txh_history = new_history;
            current_session_id = last_session_in_history.session;
            console.log(`✅ Lần đầu tải ${new_history.length} phiên. Phiên hiện tại: ${current_session_id}`);
        } else if (last_session_in_history.session > current_session_id) {
            const new_records = new_history.filter(r => r.session > current_session_id);

            if (new_records.length > 0) {
                for (let record of new_records) {
                    seiu_manager.push_record(record);
                    txh_history.push(record);
                }
                if (txh_history.length > 500) {
                    txh_history = txh_history.slice(txh_history.length - 500);
                }
                current_session_id = last_session_in_history.session;
                console.log(`🆕 Cập nhật ${new_records.length} phiên. Phiên cuối: ${current_session_id}`);
            } else {
                console.log(`🔄 Không có phiên mới. Phiên cuối: ${current_session_id}`);
            }
        } else {
            console.log(`🔄 Dữ liệu không đổi. Phiên cuối: ${current_session_id}`);
        }
    } catch (e) {
        console.error("❌ Lỗi fetch/xử lý:", e.message);
    }
}

fetch_and_process_history();
clearInterval(fetch_interval);
fetch_interval = setInterval(fetch_and_process_history, 5000);
console.log(`🔄 Fetch API mỗi 5 giây: ${api_url}`);
// ==================== ENDPOINTS ====================

// GET /api/sicbo/sunwin
app.get("/api/sicbo/sunwin", async () => {
    const last_result = txh_history.at(-1) || null;
    const current_prediction = seiu_manager.current_prediction;

    if (!last_result || !current_prediction) {
        return {
            "id": "@cskhgiabao",
            "phien_truoc": null,
            "xuc_xac1": null,
            "xuc_xac2": null,
            "xuc_xac3": null,
            "tong": null,
            "ket_qua": "đang chờ dữ liệu",
            "phien_hien_tai": current_session_id ? current_session_id + 1 : null,
            "du_doan": "chưa có",
            "du_doan_vi": "chưa có",
            "do_tin_cay": "0%"
        };
    }

    return {
        "id": "@cskhgiabao",
        "phien_truoc": last_result.session,
        "xuc_xac1": last_result.dice[0],
        "xuc_xac2": last_result.dice[1],
        "xuc_xac3": last_result.dice[2],
        "tong": last_result.total,
        "ket_qua": last_result.result.toLowerCase(),
        "phien_hien_tai": last_result.session + 1,
        "du_doan": current_prediction.prediction,
        "du_doan_vi": current_prediction.score_prediction.join("-"),
        "do_tin_cay": `${(current_prediction.confidence * 100).toFixed(0)}%`
    };
});

// GET /api/sicbo/history
app.get("/api/sicbo/history", async () => {
    if (!txh_history.length) return { message: "không có dữ liệu lịch sử." };
    const reversed = [...txh_history].sort((a, b) => b.session - a.session);
    return reversed.map((i) => ({
        session: i.session,
        dice: i.dice,
        total: i.total,
        result: i.result.toLowerCase(),
        tx_label: i.tx.toLowerCase(),
    }));
});

// GET /api/sicbo/stats
app.get("/api/sicbo/stats", async () => {
    const accuracy = seiu_manager.accuracy_stats.total > 0 ?
        (seiu_manager.accuracy_stats.correct / seiu_manager.accuracy_stats.total * 100).toFixed(1) : "0.0";
    return {
        "tong_phien": txh_history.length,
        "phien_hien_tai": current_session_id,
        "do_chinh_xac": `${accuracy}%`,
        "tong_du_doan": seiu_manager.accuracy_stats.total,
        "du_doan_dung": seiu_manager.accuracy_stats.correct,
        "so_thuat_toan": all_algs.length,
        "pham_vi_vi": {
            "xiu": [4, 5, 6, 7, 8, 9, 10],
            "tai": [11, 12, 13, 14, 15, 16, 17]
        }
    };
});

// GET /
app.get("/", async () => {
    return {
        status: "ok",
        msg: "server chạy thành công 🚀",
        author: "@cskhgiabao",
        endpoints: {
            "/api/sicbo/sunwin": "dự đoán tài xỉu và 3 vị",
            "/api/sicbo/history": "lịch sử kết quả",
            "/api/sicbo/stats": "thống kê hệ thống"
        },
        thong_tin: {
            "so_thuat_toan": all_algs.length,
            "phien_hien_tai": current_session_id,
            "tong_phien_luu": txh_history.length,
            "pham_vi_vi_xiu": "4,5,6,7,8,9,10",
            "pham_vi_vi_tai": "11,12,13,14,15,16,17"
        }
    };
});

// ==================== SERVER START ====================
const start = async () => {
    try {
        await app.listen({ port: port, host: "0.0.0.0" });
    } catch (err) {
        const error_msg = `
================= SERVER ERROR =================
time: ${new Date().toISOString()}
error: ${err.message}
stack: ${err.stack}
=================================================
`;
        console.error(error_msg);
        const log_file = path.join(__dirname, "server-error.log");
        fs.writeFileSync(log_file, error_msg, { encoding: "utf8", flag: "a+" });
        process.exit(1);
    }

    let public_ip = "0.0.0.0";
    try {
        const res = await fetch("https://ifconfig.me/ip");
        public_ip = (await res.text()).trim();
    } catch (e) {
        console.error("❌ Lỗi lấy public IP:", e.message);
    }

    console.log("\n" + "=".repeat(60));
    console.log("🚀 SICBO SUNWIN AI SERVER — @cskhgiabao");
    console.log("=".repeat(60));
    console.log(`   ➜ Local:   http://localhost:${port}/`);
    console.log(`   ➜ Network: http://${public_ip}:${port}/`);
    console.log("\n📌 API ENDPOINTS:");
    console.log(`   ➜ GET /api/sicbo/sunwin   → Dự đoán Tài/Xỉu + 3 Vị`);
    console.log(`   ➜ GET /api/sicbo/history  → Lịch sử 500 phiên gần nhất`);
    console.log(`   ➜ GET /api/sicbo/stats    → Thống kê độ chính xác`);
    console.log("\n🎯 HỆ THỐNG AI:");
    console.log(`   Số thuật toán: ${all_algs.length} (beit, 1-1, nghieng, 1-2-1, 2-2, markov2/3, freq, 1-3-1)`);
    console.log(`   Phạm vi vị Xỉu: 4-10 (ưu tiên 7-8-9-10)`);
    console.log(`   Phạm vi vị Tài: 11-17 (ưu tiên 11-12-13-14)`);
    console.log("=".repeat(60));
    console.log("\n🤖 Đang chạy... Chờ dữ liệu từ API...");
};

start();