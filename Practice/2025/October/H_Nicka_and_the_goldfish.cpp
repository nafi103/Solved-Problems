#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18+10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define endl "\n"
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

int root = 1;
vector<int>dfs_num,dfs_low,visited;
int articulation_point = -1;
vector<vector<int>>g;
int dfs_cnt = 0, root_child = 0;

void dfs(int node, int parent){
    visited[node] = true;
    dfs_num[node] = ++dfs_cnt;
    dfs_low[node] = dfs_num[node];
    for(auto &adj:g[node]){
        if(!visited[adj]){
            if(node==root)
                root_child++;
            dfs(adj,node);
            if(node!=root and dfs_low[adj]>=dfs_num[node]){
                articulation_point = node;
            }
            dfs_low[node] = min(dfs_low[node],dfs_low[adj]);
        }else if(adj!=parent){
            dfs_low[node] = min(dfs_low[node],dfs_num[adj]);
        }
    }
}

set<int>s;
multiset<int>ms;

void dfs_2(int node, int parent){
    visited[node] = true;
    dfs_num[node] = ++dfs_cnt;
    dfs_low[node] = dfs_num[node];
    for(auto &adj:g[node]){
        if(!visited[adj]){
            dfs_2(adj,node);
            if(adj!=articulation_point)
                dfs_low[node] = min(dfs_low[node],dfs_low[adj]);
        }else if(adj!=parent and adj!=articulation_point){
            dfs_low[node] = min(dfs_low[node],dfs_num[adj]);
        }
    }
    s.insert(dfs_low[node]);
    ms.insert(dfs_low[node]);
}

void solve()
{
    int n;
    cin>>n;
    dfs_num.resize(n+1);
    dfs_low.resize(n+1);
    g.resize(n+1);
    int m = n+2;
    for(int i = 0; i<m; i++){
        int u,v;
        cin>>u>>v;
        g[u].push_back(v);
        g[v].push_back(u);
    }

    visited.assign(n+1,false);
    dfs(1,-1);
    if(root_child>1)
        articulation_point = root;

    struct Ans
    {
        int tail,head,trunk;
        Ans() : tail(0),head(0),trunk(0){}
    };
    Ans ans;

    visited.assign(n+1,false);
    g[articulation_point].clear();
    for(int i = 1; i<=n; i++){
        dfs_cnt = 0;
        if(!visited[i] and i!=articulation_point){
            s.clear();
            ms.clear();
            visited[articulation_point] = false;
            dfs_2(i,-1);
            dfs_low[articulation_point] = -1;
            if(sz(s)==dfs_cnt){
                ans.tail = dfs_cnt;
            }else{
                for(auto &x: s){
                    if(ms.count(x)==1)
                        ans.trunk++;
                    else
                        ans.head+=ms.count(x);
                }
                ans.trunk+=2;
            }
        }
    }
    cout<<ans.head<<" "<<ans.trunk<<" "<<ans.tail<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}