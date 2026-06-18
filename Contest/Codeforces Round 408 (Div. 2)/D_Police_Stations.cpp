#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18 + 10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x) & (-x))
#define all(x) x.begin(), x.end()
#define endl "\n"
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x)                                        \
    cerr << "Line " << __LINE__ << ": " << #x << " = "; \
    _print(x);                                          \
    cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 void solve()
{
    int n,k,d;
    cin >> n >> k >> d;
    map<pair<int, int>, int> edge_id;
    set<int> police;
    while(k--){
        int x;
        cin >> x;
        police.insert(x);
    }
    vector<vector<int>> t(n + 1);
    for(int i = 1; i < n; i++){
        int u, v;
        cin >> u >> v;
        if(u > v)
            swap(u, v);
        t[u].push_back(v);
        t[v].push_back(u);
        edge_id[{u, v}] = i;
    }
    queue<array<int, 3>> q;
    vector<int> covered(n + 1, -1);
    for(auto &p: police){
        q.push({p, p, d});
        covered[p] = p;
    }
    set<int> remove_edge;
    while(!q.empty()){
        auto [node, par, dis] = q.front();
        q.pop();
        for (auto &adj: t[node]){
            if(adj != par){
                if(covered[adj] != -1){
                    if(node > adj){
                        remove_edge.insert(edge_id[{adj, node}]);
                    }else{
                        remove_edge.insert(edge_id[{node, adj}]);
                    }
                    continue;
                }
                covered[adj] = node;
                if (dis != 0)
                    q.push({adj, node, dis - 1});
            }
        }
    }
    cout << sz(remove_edge) << endl;
    for(auto &x: remove_edge){
        cout << x << " ";
    }
    cout << endl;
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    // cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}