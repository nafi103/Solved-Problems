#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
 using namespace std;
using namespace chrono;
using namespace __gnu_pbds;
 template <class T>
using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update>;
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
const int N = 3e5 + 10;
vector<vector<int>> t(N);
int ans = 0, rest_sum = 0;
int dmx[N], dsmx[N], mx[N], smx[N], n, k, arr[N], leaf_weight[N];
 void input(){
    cin >> n >> k;
    ans = 0, rest_sum = 0;
    for(int i = 0; i < n; i++){
        t[i].clear();
        leaf_weight[i] = 0;
        cin >> arr[i];
    }
    for(int i = 1, u, v; i < n; i++){
        cin >> u >> v;
        u--, v--;
        t[u].push_back(v);
        t[v].push_back(u);
    }
    for(int i = 0; i < n; i++){
        sort(all(t[i]), greater<int>());
    }
}
 void dfs(int node, int par){
    dmx[node] = 0;
    dsmx[node] = -inf;
    smx[node] = -1;
    mx[node] = node;
    for(auto &child: t[node]){
        if(child != par){
            dfs(child, node);
            if(dmx[child] + 1 > dmx[node] or (dmx[child] + 1 == dmx[node] and mx[child] < mx[node])) 
            {
                smx[node] = mx[node];
                dsmx[node] = dmx[node];
                                mx[node] = mx[child];
                dmx[node] = dmx[child] + 1;
            }
            else if(dmx[child] + 1 > dsmx[node] or (dmx[child] + 1 == dsmx[node] and mx[child] < smx[node]))
            {
                smx[node] = mx[child];
                dsmx[node] = dmx[child] + 1;
            }
        }
    }
}
 const pair<int,int> dummy = {-1, -1};
 void remove_leaf(int u, pbds<pair<int,int>> &leaf) {
    if (leaf_weight[u] == 0) 
        return;
    pair<int, int> p = {-leaf_weight[u], u};
    if (leaf.find(p) == leaf.end()) 
        return;
        int pos = leaf.order_of_key(p);
    if (pos < k - 1) {
        rest_sum -= leaf_weight[u];
        if (sz(leaf) > k - 1) {
            rest_sum += abs(leaf.find_by_order(k - 1)->first);
        }
    }
    leaf.erase(p);
}
 void add_leaf(int u, pbds<pair<int,int>> &leaf) {
    if (leaf_weight[u] == 0) 
        return;
    pair<int, int> p = {-leaf_weight[u], u};
        leaf.insert(p);
    int pos = leaf.order_of_key(p);
    if (pos < k - 1) {
        rest_sum += leaf_weight[u];
        if (sz(leaf) > k - 1) {
            rest_sum -= abs(leaf.find_by_order(k - 1)->first);
        }
    }
}
 void reroot(int node, int par, int passed_node, int passed_dis, pbds<pair<long long,int>> &leaf){
    int saved_mx = mx[node], saved_md = dmx[node];
    int saved_smx = smx[node], saved_smd = dsmx[node];
     if (par != -1) {
        remove_leaf(saved_mx, leaf);
        remove_leaf(passed_node, leaf);
         leaf_weight[saved_mx] -= arr[node];
        leaf_weight[passed_node] += arr[par];
         add_leaf(saved_mx, leaf);
        add_leaf(passed_node, leaf);
    }
     if(dmx[node] < passed_dis or (dmx[node] == passed_dis and passed_node < mx[node])){
        smx[node] = mx[node];
        dsmx[node] = dmx[node];
         dmx[node] = passed_dis;
        mx[node] = passed_node;
    } else if(dsmx[node] < passed_dis or (dsmx[node] == passed_dis and passed_node < smx[node])){
        smx[node] = passed_node;
        dsmx[node] = passed_dis;
    }
     ans = max(ans, arr[node] + rest_sum);
     for(auto &child: t[node]){
        if(child != par){
            if(mx[child] == mx[node]){
                reroot(child, node, smx[node], dsmx[node] + 1, leaf);
            }else{
                reroot(child, node, mx[node], dmx[node] + 1, leaf);
            }
        }
    }
     if (par != -1) {
        remove_leaf(saved_mx, leaf);
        remove_leaf(passed_node, leaf);
         leaf_weight[saved_mx] += arr[node];
        leaf_weight[passed_node] -= arr[par];
         add_leaf(saved_mx, leaf);
        add_leaf(passed_node, leaf);
    }
        mx[node] = saved_mx;
    smx[node] = saved_smx;
    dmx[node] = saved_md;
    dsmx[node] = saved_smd;
}
 void solve()
{
    input();
    if(k == 1){
        cout << *max_element(arr, arr + n) << endl;
        return;
    }
    dfs(0, -1);
    for(int i = 1; i < n; i++){
        leaf_weight[mx[i]] += arr[i];
    }
    // for(int i = 0; i < n; i++){
    //     cerr << mx[i] << " \n"[i == n - 1];
    // }
    // for(int i = 0; i < n; i++){
    //     cerr << smx[i] << " \n"[i == n - 1];
    // }
    pbds<pair<int,int>> leaf;
    for(int i = 0; i < n; i++){
        if(leaf_weight[i]){
            leaf.insert({-leaf_weight[i], i});
        }
    }
    for(int i = 0; i < min(sz(leaf), k - 1); i++){
        auto &tmp = *leaf.find_by_order(i);
        rest_sum += abs(tmp.first);
    }
    ans = max(ans, arr[0] + rest_sum);
    reroot(0, -1, -1, - 2 * inf, leaf);
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