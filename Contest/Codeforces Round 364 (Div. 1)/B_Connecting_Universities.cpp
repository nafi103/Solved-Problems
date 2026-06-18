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
 const int N = 2e5 + 10;
int value[N], ans = 0, k;
vector<int> g[N];
 void dfs(int node, int parent){
    for(auto &child: g[node]){
        if(child != parent){
            dfs(child, node);
            ans += min(value[child], k - value[child]);
            value[node] += value[child];
        }
    }
}
 void solve()
{
    int n, root = 0;
    cin >> n >> k;
    k <<= 1;
    for(int i = 0, x; i < k; i++){
        cin >> x;
        x--;
        value[x] = 1;
        root = x;
    }
     for(int i = 1, u, v; i < n; i++){
        cin >> u >> v;
        u--, v--;
        g[u].push_back(v);
        g[v].push_back(u);
    }
     dfs(root, -1);
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
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}