#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <random>
#include <vector>
using Int = int;  // clang-format off
#define REP_(i, a_, b_, a, b, ...) for (Int i = (a), lim##i = (b); i < lim##i; i++)
#define REP(i, ...) REP_(i, __VA_ARGS__, __VA_ARGS__, 0, __VA_ARGS__)
#define ALL(v) std::begin(v), std::end(v)
struct SetupIO { SetupIO() { std::cin.tie(nullptr), std::ios::sync_with_stdio(false), std::cout << std::fixed << std::setprecision(13); } } setup_io;
#ifndef dump
#define dump(...)
#endif  // clang-format on

/**
 *    author:  knshnb
 *    created: Sun Jun 28 20:59:50 JST 2020
 **/

template <class T> bool chmin(T& a, const T& b) { return a > b ? a = b, true : false; }
template <class T> bool chmax(T& a, const T& b) { return a < b ? a = b, true : false; }

uint64_t rnd() {
    static uint64_t x = std::mt19937(std::chrono::steady_clock::now().time_since_epoch().count())();
    x += 0x9e3779b97f4a7c15;
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9;
    x = (x ^ (x >> 27)) * 0x94d049bb133111eb;
    return x ^ (x >> 31);
}

struct Timer {
    std::chrono::system_clock::time_point start_time;
    Timer() : start_time(std::chrono::system_clock::now()) {}
    double operator()() {
        return std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now() - start_time)
            .count();
    }
};

constexpr Int D = 365;
constexpr Int K = 26;
Int s[D][K], c[K];
Int sum;
constexpr double TIME_LIMIT = 1980;

struct Schedule {
    std::array<Int, D> a;
    Int score = 0;
    Int calc_score(Int D_ = D) const {
        Int ret = 0;
        Int cur_minus = 0;
        static std::array<Int, K> last;
        REP(k, K) last[k] = -1;
        REP(d, D_) {
            cur_minus += sum - c[a[d]] * (d - last[a[d]]);
            ret += s[d][a[d]] - cur_minus;
            last[a[d]] = d;
        }
        return ret;
    }
    Schedule generate_neighbor() const {
        Schedule ret = *this;
        if (rnd() % 2) {
            Int dif = rnd() % 15 + 1;
            Int idx = rnd() % (D - dif);
            std::swap(ret.a[idx], ret.a[idx + dif]);
        } else {
            Int idx = rnd() % D;
            ret.a[idx] = rnd() % K;
        }
        ret.score = ret.calc_score();
        return ret;
    }
    void change1(Int d, Int k) {}
};

struct ScheduleDif : Schedule {
    std::array<std::vector<Int>, K> ds;
    ScheduleDif() {}
    ScheduleDif(const Schedule& sc) {
        score = sc.score, a = sc.a;
        REP(k, K) ds[k].push_back(-1);
        REP(d, D) ds[sc.a[d]].push_back(d);
        REP(k, K) ds[k].push_back(D);
    }
    Int balance(Int d, Int prv, Int nxt) const {
        auto calc = [](Int dif) { return dif * (dif - 1) / 2; };
        return calc(d - prv) + calc(nxt - d) - calc(nxt - prv);
    }
    Int score_dif(Int d, Int k) const {
        if (a[d] == k) return 0;
        Int ret = 0;
        ret += s[d][k] - s[d][a[d]];
        // erase d from ds[prv_k]
        {
            const std::vector<Int>& v = ds[a[d]];
            Int i = std::lower_bound(v.begin(), v.end(), d) - v.begin();
            // assert(v[i] == d);
            ret += balance(d, v[i - 1], v[i + 1]) * c[a[d]];
        }
        // insert d into ds[k]
        {
            const std::vector<Int>& v = ds[k];
            Int i = std::lower_bound(v.begin(), v.end(), d) - v.begin();
            // assert(i == v.size() || v[i] > d);
            ret -= balance(d, v[i - 1], v[i]) * c[k];
        }
        return ret;
    }
    Int score_dif_swap(Int d1, Int d2) const {
        // assert(d1 < d2);
        Int k1 = a[d1], k2 = a[d2];
        Int ret = 0;
        ret += (s[d1][k2] - s[d1][k1]) + (s[d2][k1] - s[d2][k2]);
        {
            const std::vector<Int>& v = ds[k1];
            // erase d1 from ds[k1]
            Int i1 = std::lower_bound(v.begin(), v.end(), d1) - v.begin();
            ret += balance(d1, v[i1 - 1], v[i1 + 1]) * c[k1];
            // insert d2 into ds[k1]
            Int i2 = std::lower_bound(v.begin(), v.end(), d2) - v.begin();
            ret -= balance(d2, v[i2 - 1] == d1 ? v[i2 - 2] : v[i2 - 1], v[i2]) * c[k1];
        }
        {
            const std::vector<Int>& v = ds[k2];
            // insert d1 into ds[k2]
            Int i1 = std::lower_bound(v.begin(), v.end(), d1) - v.begin();
            ret -= balance(d1, v[i1 - 1], v[i1] == d2 ? v[i1 + 1] : v[i1]) * c[k2];
            // erase d2 from ds[k2]
            Int i2 = std::lower_bound(v.begin(), v.end(), d2) - v.begin();
            ret += balance(d2, v[i2 - 1], v[i2 + 1]) * c[k2];
        }
        return ret;
    }
    // a[d] <- k
    void change1(Int d, Int k) {
        if (a[d] == k) return;
        Int prv_k = a[d];
        a[d] = k;
        // erase d from ds[prv_k]
        {
            std::vector<Int>& v = ds[prv_k];
            Int i = std::lower_bound(v.begin(), v.end(), d) - v.begin();
            // assert(v[i] == d);
            v.erase(v.begin() + i);
        }
        // insert d into ds[k]
        {
            std::vector<Int>& v = ds[k];
            Int i = std::lower_bound(v.begin(), v.end(), d) - v.begin();
            // assert(v[i] != d);
            v.insert(v.begin() + i, d);
            // assert(v[i] == d);
        }
    }
};

Schedule greedy_initialize() {
    Schedule ret;
    std::array<Int, K> last;
    REP(k, K) last[k] = -1;
    REP(d, D) {
        Int ma = -1, use = -1;
        REP(k, K) {
            Int ad = s[d][k] + c[k] * (d - last[k]) + c[k] * 15;  // heuristic value function
            if (chmax(ma, ad)) use = k;
        }
        ret.a[d] = use;
        last[use] = d;
    }
    ret.score = ret.calc_score();
    return ret;
}

Schedule periodic_initialize(Int offset = 0) {
    Schedule ret;
    REP(d, D) ret.a[d] = (d + offset) % K;
    ret.score = ret.calc_score();
    return ret;
}

template <class State, bool use_dif = true> struct Annealing {
    constexpr static Int INF = 1e9;
    State cur;
    State best_state;
    const double start_temp, end_temp;
    Timer timer;
    Annealing(State state, double start_temp_ = 50, double end_temp_ = 10)
        : cur(state), start_temp(start_temp_), end_temp(end_temp_) {}
    bool should_stay(Int score_dif, double cur_time, double time_lim) {
        double temperature = start_temp + (end_temp - start_temp) * cur_time / time_lim;
        double prob = std::exp(score_dif / temperature);
        return prob * INF < rnd() % INF;
    }
    bool update(double cur_time, double time_lim) {
        State nxt = cur.generate_neighbor();
        bool is_update = !should_stay(nxt.calc_score() - cur.calc_score(), cur_time, time_lim);
        if (is_update) {
            cur = std::move(nxt);
        }
        return is_update;
    }
    bool update_by_dif(double cur_time, double time_lim) {
        if (rnd() % 2 == 0) {
            // change 1 day
            Int d = rnd() % D, k = rnd() % K;
            Int prv_k = cur.a[d];
            while (k == prv_k) k = rnd() % K;
            Int score_dif = cur.score_dif(d, k);
            bool is_update = !should_stay(score_dif, cur_time, time_lim);
            if (is_update) {
                cur.change1(d, k);
                cur.score += score_dif;
            }
            return is_update;
        } else {
            // swap 2 days
            Int dif = rnd() % 15 + 1;
            Int d1 = rnd() % (D - dif), d2 = d1 + dif;
            while (cur.a[d1] == cur.a[d2]) dif = rnd() % 15 + 1, d1 = rnd() % (D - dif), d2 = d1 + dif;
            Int score_dif = cur.score_dif_swap(d1, d2);
            bool is_update = !should_stay(score_dif, cur_time, time_lim);
            if (is_update) {
                Int prv_k1 = cur.a[d1], prv_k2 = cur.a[d2];
                cur.change1(d1, prv_k2);
                cur.change1(d2, prv_k1);
                cur.score += score_dif;
            }
            return is_update;
        }
    }
    // return iteration num until time limit
    Int run(double time_lim) {
        for (Int t = 0;; t++) {
            double cur_time = timer();
            if (cur_time > time_lim) return t;
            Int prv_score = cur.score;
            if (use_dif) {
                update_by_dif(cur_time, time_lim);
            } else {
                update(cur_time, time_lim);
            }
            if (cur.score > best_state.score) best_state = cur;
            if (prv_score != cur.score) dump(t, prv_score, cur.score);
        }
    }
};

Int solve() {
    Timer timer;
    // input
    Int _;
    std::cin >> _;
    sum = 0;
    REP(i, K) std::cin >> c[i], sum += c[i];
    REP(i, D) REP(j, K) std::cin >> s[i][j];

    // local search
    double rem_time = TIME_LIMIT - timer();
    constexpr Int annealing_num = 1;
    Int ma = -1e9;
    ScheduleDif ans;
    REP(x, annealing_num) {
        Annealing<ScheduleDif, true> an(x == 0 ? greedy_initialize() : periodic_initialize(x), 1500, 10);
        std::cerr << an.run(rem_time / annealing_num) << " iterations\n";
        assert(an.cur.score == an.cur.calc_score());
        if (chmax(ma, an.best_state.score)) ans = std::move(an.best_state);
    }

    // output
    for (Int x : ans.a) std::cout << x + 1 << "\n";
    std::cout << std::endl;
    dump(ans.score);
    return ans.score + (Int)1e6;
}

signed main() {
#ifdef _LOCAL
    Int T = 10;
    Int score = 0;
    REP(i, T) {
        std::string filename = "data/";
        filename += ('0' + i);
        filename += ".txt";
        std::ifstream in(filename);
        std::cin.rdbuf(in.rdbuf());
        score += std::max(0, solve());
    }
    std::cerr << "sum : " << score << std::endl;
#else
    solve();
#endif
}
