#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)     \
    for (auto &x : v) \
    cout << x << " "; \
    cout<<endl
#define endl "\n"
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl
#define remove_punctuation(text) regex_replace(text, regex(R"([^\w\s])"), "")
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

struct S {
    int value;

    S(int val = 0) : value(val) {}
};

S combine(const S &a, const S &b) {
    return S(a.value + b.value);
}

struct Segment_Tree {
    int n;
    vector<S> t, lazy;

    Segment_Tree(int _n) {
        n = _n;
        t.resize(2 * n, S());
        lazy.resize(2 * n, S());
    }

    void apply(int p, int val, int len) {
        t[p].value ^= val * len;
        if (p < n) lazy[p].value ^= val;
    }

    void push(int p, int len) {
        apply(p << 1, lazy[p].value, len / 2);
        apply(p << 1 | 1, lazy[p].value, len / 2);
        lazy[p] = S();
    }

    void build() {
        for (int i = n - 1; i > 0; --i) {
            t[i] = combine(t[i << 1], t[i << 1 | 1]);
        }
    }

    void update(int l, int r, int val) {
        int L = l, R = r, len = 1;
        for (l += n, r += n; l < r; l >>= 1, r >>= 1, len <<= 1) {
            if (l & 1) apply(l++, val, len);
            if (r & 1) apply(--r, val, len);
        }
    }

    void push_down(int l, int r) {
        int h = __builtin_ctz(n);
        for (int i = h; i > 0; --i) {
            if ((l >> i) < n) push(l >> i, 1 << (i - 1));
            if ((r >> i) < n) push(r >> i, 1 << (i - 1));
        }
    }

    S query(int l, int r) {
        push_down(l + n, r + n);
        S resl, resr;
        for (l += n, r += n; l < r; l >>= 1, r >>= 1) {
            if (l & 1) resl = combine(resl, t[l++]);
            if (r & 1) resr = combine(t[--r], resr);
        }
        return combine(resl, resr);
    }
};

void solve()
{
    
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}