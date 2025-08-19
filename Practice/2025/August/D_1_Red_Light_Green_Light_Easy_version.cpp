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
vector<int>visited, cell, d;
int n,k;

bool dfs(int last_cell, int last_time, int dir){
    int curr_cell = last_cell+dir;
    if(curr_cell<0 or curr_cell==n){
        return true;
    }
    int curr_time = abs(cell[curr_cell] - cell[last_cell]) + last_time;
    if(curr_time%k==d[curr_cell]){
        visited[curr_cell]++;
        dir*=-1;
    }
    if(visited[curr_cell]>2 and curr_time>=k){
        return false;
    }
    return dfs(curr_cell,curr_time,dir);
}

void solve()
{
    d.clear();
    cell.clear();
    visited.clear();
    cin>>n>>k;
    cell.resize(n);
    d.resize(n);
    readv(cell);
    readv(d);
    int q;
    cin>>q;
    while(q--){
        visited.assign(n,0);
        int start;
        cin>>start;
        int src = -1, t;
        for(int i = 0; i<n; i++){
            if(cell[i]<start)
                continue;
            if((cell[i]-start)%k==d[i]){
                src = i;
                t = cell[i]-start;
                break;
            }
        }
        if(src==-1){
            cout<<"YES"<<endl;
            continue;
        }
        if(dfs(src,t,-1)){
            cout<<"YES"<<endl;
        }else{
            cout<<"NO"<<endl;
        }
    }
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