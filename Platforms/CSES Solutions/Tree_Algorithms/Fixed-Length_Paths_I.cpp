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

int n, k, ans;
vector<vector<int>> t;
vector<int> level;
vector<map<int,int>> subtree_level;

void input(){
    ans = 0;
    cin >> n >> k;
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
    if(big_child != -1){
        swap(subtree_level[node], subtree_level[big_child]);
        if(subtree_level[node].count(level[node] + k))
            ans += subtree_level[node][level[node] + k];
    }
    subtree_level[node][level[node]]++;
    for(auto &child: t[node]){
        if(child != par and child != big_child){
             for(auto &[f, s]: subtree_level[child]){
                int target_level = 2 * level[node] + k - f;
                if(subtree_level[node].count(target_level)){
                    ans += s * subtree_level[node][target_level];
                }
             }
             for(auto &[f, s]: subtree_level[child])
                subtree_level[node][f] += s;
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