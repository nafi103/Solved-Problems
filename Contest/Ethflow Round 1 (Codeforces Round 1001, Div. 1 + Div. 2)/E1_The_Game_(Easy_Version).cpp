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
 const int N = 4e5 + 10;
int n, w[N], mx[N], target_node, target_node_value;
vector<vector<int>> t(N);
 void input(){
    cin >> n;
    for(int i = 0; i < n; i++){
        cin >> w[i];
        mx[i] = -inf;
        t[i].clear();
    }
    int u, v;
    for(int i = 1; i < n; i++){
        cin >> u >> v;
        u--, v--;
        t[u].push_back(v);
        t[v].push_back(u);
    }
    target_node = -1;
    target_node_value = -1;
}
 void find_max_in_subtree(int node, int par){
    mx[node] = w[node];
    for(auto &child: t[node]){
        if(child ^ par){
            find_max_in_subtree(child, node);
            mx[node] = max(mx[node], mx[child]);
        }
    }
}
 void reroot(int node, int par, int par_max){
    if(w[node] < par_max and target_node_value < w[node]){
        target_node = node;
        target_node_value = w[node];
    }
    multiset<int> child_max;
    for(auto &child: t[node]){
        if(child != par){
            child_max.insert(mx[child]);
        }
    }
    for(auto &child: t[node]){
        if(child != par){
            int rmv = mx[child];
            child_max.erase(child_max.find(rmv));
            reroot(child, node, max({w[node], par_max, (!child_max.empty() ? *child_max.rbegin() : -inf)}));
            child_max.insert(rmv);
        }
    }
}
 void solve()
{
    input();
    find_max_in_subtree(0, -1);
    reroot(0, -1, -inf);
    cout << target_node + 1 << endl;
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