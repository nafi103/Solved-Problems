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
 struct DSU{
    int n;
    vector<int> parent, _size;
     DSU(int _n){
        n = _n;
        parent.resize(n);
        _size.assign(n, 1);
        iota(all(parent), 0);
    }
     int find(int a){
        if(parent[a] == a)
            return a;
        return parent[a] = find(parent[a]);
    }
     int Union(int a, int b){
        a = find(a);
        b = find(b);
        if(a == b)
            return 0;
        int sz_a = _size[a], sz_b = _size[b];
        if(_size[a] < _size[b])
            swap(a, b);
        parent[b] = a;
        _size[a] += _size[b];
        return (sz_a * sz_b - 1);
    }
};
 int expo(int a, int b){
    int res = 1;
    while(b > 0){
        if(b & 1)
            res = (res * a) % mod;
        a = (a * a) % mod;
        b >>= 1;
    }
    return res;
}
 void solve()
{
    int n, S, ans = 1;
    cin >> n >> S;
    vector<array<int,3>> edges;
    edges.reserve(n - 1);
    for(int i = 1, u, v, w; i < n; i++){
        cin >> u >> v >> w;
        u--, v--;
        edges.push_back({w, u, v});
    }
    sort(all(edges));
    DSU uf(n);
    for(auto &[w, u, v]: edges){
        int extra_edges = uf.Union(u, v);
        if(extra_edges){
            ans = (ans * expo(S - w + 1, extra_edges)) % mod;
        }
    }
    cout << ans << endl;
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