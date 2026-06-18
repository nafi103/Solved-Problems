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

int n, k1, k2, ans;
vector<vector<int>> t;
vector<int> level;
vector<pbds<pair<int,int>>> subtree_level;

void input(){
    ans = 0;
    cin >> n >> k1 >> k2;
    t.resize(n);
    level.resize(n);
    subtree_level.resize(n);
    int u, v;
    for(int i = 1; i < n ;i++){
        cin >> u >> v;
        u--, v--;
        t[u].push_back(v);
        t[v].push_back(u);
    }
}

void find_level(int node, int par, int l){
    level[node] = l;
    for(auto &child: t[node]){
        if(child ^ par){
            find_level(child, node, l + 1);
        }
    }
}

void dfs(int node, int par){
    int big_child = -1, big_child_size = -1;
    for(auto &child: t[node]){
        if(child ^ par){
            dfs(child, node);
            if(sz(subtree_level[child]) > big_child_size){
                big_child_size = sz(subtree_level[child]);
                big_child = child;
            }
        }
    }
    pbds<pair<int,int>> &os = subtree_level[node];
    if(big_child != -1){
        os.swap(subtree_level[big_child]);
        int lb = level[node] + k1, ub = level[node] + k2;
        auto itr = os.upper_bound({ub, inf});
        auto itl = os.lower_bound({lb, -inf});
        int r = (itr == os.end() ? sz(os) : os.order_of_key(*itr));
        int l = (itl == os.end() ? sz(os) : os.order_of_key(*itl));
        ans += (r - l);
    }
    os.insert({level[node], node});
    for(auto &child: t[node]){
        if(child != par and child != big_child){
             for(auto &[f, s]: subtree_level[child]){
                int lb = 2 * level[node] + k1 - f, ub = 2 * level[node] + k2 - f;
                auto itr = os.upper_bound({ub, inf});
                auto itl = os.lower_bound({lb, -inf});
                int r = (itr == os.end() ? sz(os) : os.order_of_key(*itr));
                int l = (itl == os.end() ? sz(os) : os.order_of_key(*itl));
                ans += (r - l);
             }
             for(auto &x: subtree_level[child])
                os.insert(x);
        }
    }
}

void solve()
{
    input();
    find_level(0, -1, 0);
    dfs(0, -1);
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