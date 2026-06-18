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
 bool all_even;
vector<vector<int>> t;
int n, leaf, has_leaf;
 void input(){
    cin >> n;
    t.resize(n);
    for(int i = 1, u, v; i < n; i++){
        cin >> u >> v;
        u--, v--;
        t[u].push_back(v);
        t[v].push_back(u);
    }
    all_even = true;
    leaf = 0; has_leaf = 0;
}
 void dfs(int node, int par, int d){
    if(sz(t[node]) == 1 and (d & 1))
        all_even = false;
    bool leaf_present = false;
    leaf += sz(t[node]) == 1;
    for(auto &child: t[node]){
        leaf_present |= (sz(t[child]) == 1);
        if(child != par){
            dfs(child, node, d + 1);
        }
    }
    has_leaf += leaf_present;
}
 void solve()
{
    input();
    int root = -1;
    for(int i = 0; i < n; i++){
        if(sz(t[i]) == 1){
            root = i;
            break;
        }
    }
    dfs(root, -1, 0);
    int mn = (all_even ? 1 : 3);
    int mx = n - 1 - leaf + has_leaf;
    cout << mn << " " << mx << endl;
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