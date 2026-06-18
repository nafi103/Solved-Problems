#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 struct Trie {
    struct Node {
        int next[2];
        int pass = 0;
        int end = 0;
                Node() { 
            memset(next, -1, sizeof(next)); 
        }
    };
        vector<Node> t;
     Trie() {
        t.assign(1, Node()); 
    }
     void insert(const int& x) {
        int v = 0;
        for(int i = 29; i >= 0; i--){
            int c = (x >> i) & 1;
            if (t[v].next[c] == -1) {
                t[v].next[c] = t.size();
                t.emplace_back();
            }
            v = t[v].next[c];
            t[v].pass++;
        }
        t[v].end++;
    }
};
 struct Mint {
    int v;
    explicit operator int() const { return v; }
    Mint() { v = 0; }
    Mint(int _v) : v(_v % mod) { v += (v < 0) * mod; }
};
 Mint &operator+=(Mint &a, Mint b) {
    if ((a.v += b.v) >= mod) a.v -= mod;
    return a;
}
 Mint &operator-=(Mint &a, Mint b) {
    if ((a.v -= b.v) < 0) a.v += mod;
    return a;
}
 Mint operator+(Mint a, Mint b) { return a += b; }
Mint operator-(Mint a, Mint b) { return a -= b; }
Mint operator*(Mint a, Mint b) { return Mint(a.v * b.v); }
Mint &operator*=(Mint &a, Mint b) { return a = a * b; }
 Mint pow(Mint a, int p) {
    assert(p >= 0);
    Mint res = 1;
    while (p > 0) {
        if (p & 1) res *= a;
        a *= a;
        p >>= 1;
    }
    return res;
}
 Mint inv(Mint a) {
    assert(a.v != 0);
    return pow(a, mod - 2);
}
 Mint operator/(Mint a, Mint b) { return a * inv(b); }
 void calc(int v, int k, Mint &up, Trie &trie){
    if(trie.t[v].next[0] != -1 and trie.t[v].next[1] != -1){
        Mint cnt0 = trie.t[trie.t[v].next[0]].pass;
        Mint cnt1 = trie.t[trie.t[v].next[1]].pass;
        int i = k + 1;
        up += Mint((2 * (i / 2) + 1)) * cnt0 * cnt1;
        up += Mint(2 * ((i + 1) / 2)) * cnt0 * cnt1;
    }
    if(trie.t[v].end > 0){
        int i = k + 1;
        up += Mint(i * trie.t[v].end * trie.t[v].end);
    }
    if(trie.t[v].next[0] != -1)
        calc(trie.t[v].next[0], k, up, trie);
    if(trie.t[v].next[1] != -1)
        calc(trie.t[v].next[1], k + 1, up, trie);
}
 void solve()
{
    int n;
    cin >> n;
    Trie trie;
    for(int i = 0, x; i < n; i++){
        cin >> x;
        trie.insert(x);
    }
    Mint up = 0;
    calc(0, 0, up, trie);
    Mint nn = Mint(n * n);
    Mint ans = up / nn;
    cout << ans.v << endl;
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}