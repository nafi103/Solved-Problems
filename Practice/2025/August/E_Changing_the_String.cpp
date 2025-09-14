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
int cb;

bool query(int b,vector<vector<deque<int>>>&edge){
    int c = 3-b;
    if(!edge[b][0].empty()){
        edge[b][0].pop_front();
        return true;
    }
    while(!edge[b][c].empty() and !edge[c][0].empty() and edge[b][c].back()>edge[c][0].back()){
        edge[b][c].pop_back();
        if(b==2 and c==1)
            cb++;
    }
    if(!edge[b][c].empty() and !edge[c][0].empty()){
        edge[c][0].pop_back();
        edge[b][c].pop_back();
        return true;
    }
    return false;
}

void solve()
{
    cb = 0;
    int n,m;
    string str;
    cin>>n>>m>>str;
    vector<pair<int,int>>q(m);
    vector<vector<deque<int>>>edge(3,vector<deque<int>>(3));
    vector<int> istr(n);
    for(int i = 0; i<n; i++){
        istr[i] = str[i] - 'a';
    }
    for(int i = 0; i<m; i++){
        auto &[u,v] = q[i];
        char x,y;
        cin>>x>>y;
        u = x-'a'; v = y-'a';
        edge[u][v].push_back(i);
    }
    for(int i = 0; i<n; i++){
        if(istr[i]==1){
            if(query(1,edge))
                istr[i] = 0;
        }else if(istr[i]==2){
            if(query(2,edge))
                istr[i] = 0;
            else if(cb){
                cb--;
                istr[i] = 1;
            }else if(!edge[2][1].empty()){
                edge[2][1].pop_back();
                istr[i] = 1;
            }
        }
        cout<<(char)('a'+istr[i]);
    }
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
    cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}