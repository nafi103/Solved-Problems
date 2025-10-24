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
vector<int>value;
vector<map<int,int>>sack;
vector<int>ans;

void dfs(int node, int parent){
    sack[node][value[node]]++;

    int bigChild = -1, mx = -1, node_ans = value[node], cnt = 1;

    for(auto &child: t[node]){
        if(child!=parent){
            dfs(child,node);
            if(cnt<sack[child][ans[child]]){
                node_ans = ans[child];
                cnt = sack[child][ans[child]];
            }else if(cnt==sack[child][ans[child]]){
                node_ans = min(node_ans, ans[child]);
            }
            if(sz(sack[child])>mx){
                mx = sz(sack[child]);
                bigChild = child;
            }
        }
    }

    if(bigChild!=-1)
        swap(sack[node],sack[bigChild]);

    for(auto &child: t[node]){
        if(child!=parent){
            for(auto &[f,s]: sack[child]){
                sack[node][f]+=s;
                if(sack[node][f]>cnt){
                    node_ans = f;
                    cnt = sack[node][f];
                }else if(sack[node][f]==cnt){
                    node_ans = min(node_ans,f);
                }
            }
            sack[child].clear();
        }
    }

    ans[node] = node_ans;
}

void solve()
{
    int n,u,v,root;
    cin>>n;
    sack.resize(n);
    value.resize(n);
    ans.resize(n);
    readv(value);
    t.resize(n);
    vector<int>in_degree(n,0);
    for(int i = 1; i<n; i++){
        cin>>u>>v;
        u--,v--;
        t[u].push_back(v);
        in_degree[v]++;
    }
    for(int i = 0; i<n; i++){
        if(in_degree[i]==0){
            root = i;
            break;
        }
    }
    dfs(root,-1);
    for(auto &x: ans)
        cout<<x<<" ";
    cout<<endl;
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