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
vector<vector<int>>t;
int dnode, dis;
vector<int> _distance;

void diameter_dfs(int node, int par, int d){
    _distance[node] = d;
    if(d>dis){
        dis = d;
        dnode = node;
    }
    for(auto &child: t[node]){
        if(child!=par){
            diameter_dfs(child,node,d+1);
        }
    }
}

void solve()
{
    _distance.clear();
    t.clear();
    int n;
    cin>>n;
    _distance.assign(n+1,0);
    t.resize(n+1);
    for(int i = 1; i<n; i++){
        int u,v;
        cin>>u>>v;
        t[u].push_back(v);
        t[v].push_back(u);
    }
    if(n<=3){
        cout<<-1<<endl;
        return;
    }
    dis = -1;
    diameter_dfs(1,-1,0);
    int diameter_node1 = dnode;
    dis = -1;
    _distance.assign(n+1,0);
    diameter_dfs(diameter_node1,-1,0);
    int diameter_node2 = dnode;
    vector<bool>in_diameter(n+1,false);
    int curr_node = diameter_node2;
    in_diameter[diameter_node1] = true;
    while(curr_node!=diameter_node1){
        in_diameter[curr_node] = true;
        for(auto &child: t[curr_node]){
            if(_distance[child]==_distance[curr_node]-1){
                curr_node = child;
                break;
            }
        }
    }
    swap(diameter_node1,diameter_node2);
    while(diameter_node1!=diameter_node2){
        if(sz(t[diameter_node1])>=3){
            int b = diameter_node1, c , a;
            for(auto &child: t[diameter_node1]){
                if(_distance[child]==_distance[diameter_node1]-1){
                    a = child;
                }else if(!in_diameter[child]){
                    c = child;
                }
            }
            cout<<a<<" "<<b<<" "<<c<<endl;
            return;
        }else{
            for(auto &child: t[diameter_node1]){
                if(_distance[child]==_distance[diameter_node1]-1){
                    diameter_node1 = child;
                    break;
                }
            }
        }
    }
    cout<<-1<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}