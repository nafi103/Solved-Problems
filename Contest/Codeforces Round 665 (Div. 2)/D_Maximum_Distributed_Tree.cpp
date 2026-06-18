#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 1e9 + 7;
const int inf = 1e18 + 10;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 const int N = 1e5 + 10, M = 1e4 + 10;
vector<vector<int>> t(N);
int n, m, parent[N], subtree[N];
vector<pair<int,int>> edges;
deque<int> p;
 void input(){
    p.clear();
    edges.clear();
    cin >> n;
    for(int i = 0; i < n; i++){
        t[i].clear();
        subtree[i] = 1; 
    }
    for(int i = 1, u, v; i < n; i++){
        cin >> u >> v;
        u--, v--;
        edges.push_back({u, v});
        t[u].push_back(v);
        t[v].push_back(u);
    }
    cin >> m;
    p.resize(m);
    for(int i = 0; i < m; i++)
        cin >> p[i];
    sort(all(p), greater<int>());
    while(sz(p) > n - 1){
        int x = p.front();
        p.pop_front();
        p[0] = (p[0] * x) % mod;
    }
}
 void dfs(int node, int par){
    parent[node] = par;
    for(auto &child: t[node]){
        if(child != par){
            dfs(child, node);
            subtree[node] += subtree[child];
        }
    }
}
 void solve()
{
    input();
    dfs(0, -1);
    vector<int> bridge;
    bridge.reserve(n);
    for(auto &[u, v]: edges){
        if(parent[v] != u)
            swap(u, v);
        int left = subtree[v], right = n - left;
        bridge.push_back(left * right);
    }
    sort(all(bridge), greater<int>());
    int ans = 0;
    for(int i = 0; i < n - 1; i++){
        if(i < m)
            ans = (ans + (bridge[i] * p[i]) % mod) % mod;
        else
            ans = (ans + bridge[i]) % mod;
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