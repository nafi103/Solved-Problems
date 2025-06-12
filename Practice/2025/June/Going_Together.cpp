#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

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
bool visited[10][10][10][10][10][10];
int n;
int x[] = {1,-1,0,0};
int y[] = {0,0,1,-1};
vector<vector<char>>grid;

bool valid(int i, int j){
    return i>=0 and i<n and j>=0 and j<n and grid[i][j]!='#';
}

void solve()
{
    grid.clear();
    cin>>n;
    vector<int>ini;
    ini.reserve(6);
    grid.resize(n,vector<char>(n));
    int k = 0;
    for(int i = 0; i<n; i++){
        for(int j = 0; j<n; j++){
            cin>>grid[i][j];
            if(grid[i][j]=='A' or grid[i][j]=='B' or grid[i][j]=='C'){
                ini.push_back(i);
                ini.push_back(j);
            }
        }
    }
    memset(visited,false,sizeof visited);
    queue<array<int,7>>q;
    q.push({0,ini[0],ini[1],ini[2],ini[3],ini[4],ini[5]});
    visited[ini[0]][ini[1]][ini[2]][ini[3]][ini[4]][ini[5]] = true;
    while(!q.empty()){
        auto [d,fx,fy,sx,sy,tx,ty] = q.front();
        q.pop();
        if(grid[fx][fy] == 'X' and grid[sx][sy] == 'X' and grid[tx][ty] == 'X'){
            cout << d << endl;
            return;
        }
        for(int i = 0; i<4; i++){
            int nfx = fx, nfy = fy, nsx = sx, nsy = sy, ntx = tx, nty = ty;
            if(valid(fx+x[i], fy+y[i])){
                nfx = fx+x[i];
                nfy = fy+y[i];
            }
            if(valid(sx+x[i], sy+y[i])){
                nsx = sx+x[i];
                nsy = sy+y[i];
            }
            if(valid(tx+x[i], ty+y[i])){
                ntx = tx+x[i];
                nty = ty+y[i];
            }
            if(nfx == nsx and nfy == nsy) {
                nfx = fx; nfy = fy;
                nsx = sx; nsy = sy;
            }
            if(nsx == ntx and nsy == nty) {
                nsx = sx; nsy = sy;
                ntx = tx; nty = ty;
            }
            if(nfx == ntx and nfy == nty) {
                nfx = fx; nfy = fy;
                ntx = tx; nty = ty;
            }
            if((nfx == nsx and nfy == nsy) or (nfx == ntx and nfy == nty) or (nsx == ntx and nsy == nty))
                continue;
            if(!visited[nfx][nfy][nsx][nsy][ntx][nty]){
                visited[nfx][nfy][nsx][nsy][ntx][nty]  = true;
                q.push({d+1,nfx,nfy,nsx,nsy,ntx,nty});
            }
        }
    }
    cout<<"trapped"<<endl;
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
        cout<<"Case "<<z<<": ";
        solve();
    }
}