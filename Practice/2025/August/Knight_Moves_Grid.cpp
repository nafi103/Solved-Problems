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
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)     \
    for (auto &x : v) \
    cout << x << " "; \
    cout<<endl
#define endl "\n"
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl
#define remove_punctuation(text) regex_replace(text, regex(R"([^\w\s])"), "")
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

int n;
bool valid(int i, int j){
    return i>=0 and i<n and j>=0 and j<n;
}

int dx[] = {2, 1, -1, -2, -2, -1, 1, 2};
int dy[] = {1, 2, 2, 1, -1, -2, -2, -1};

void solve()
{
    cin>>n;
    vector<vector<int>>ans(n,vector<int>(n,inf));
    queue<array<int,3>>q;
    q.push({0,0,0});
    ans[0][0]= 0;
    while(!q.empty()){
        auto [d,x,y] = q.front();
        q.pop();
        for(int i = 0; i<8; i++){
            int nx = x+dx[i], ny = y+dy[i];
            if(valid(nx,ny) and ans[nx][ny]>d+1){
                ans[nx][ny] = d+1;
                q.push({d+1,nx,ny});
            }
        }
    }
    for(int i = 0; i<n; i++){
        for(int j = 0; j<n; j++){
            cout<<ans[i][j]<<" ";
        }
        cout<<endl;
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
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}