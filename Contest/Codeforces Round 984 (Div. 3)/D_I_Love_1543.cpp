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
int n,m;

vector<string> spirallyTraverse(vector<vector<char>>& mat) {
    vector<string> res;
    vector<vector<bool> > vis(n, vector<bool>(m, false));
    int dr[] = { 0, 1, 0, -1 };
    int dc[] = { 1, 0, -1, 0 };
    int r = 0, c = 0,idx = 0;
    string str = "";
    for (int i = 0; i < m * n; ++i) {
        str.push_back(mat[r][c]);
        vis[r][c] = true;
        int newR = r + dr[idx];
        int newC = c + dc[idx];
        if (0 <= newR && newR < n && 0 <= newC && newC < m
            && !vis[newR][newC]) {
            r = newR;
            c = newC;
        }
        else {
            if(newR==newC and vis[newR][newC] and sz(str)){
                debug(str)
                res.pb(str);
                str = "";
            }
            idx = (idx + 1) % 4;
            r += dr[idx];
            c += dc[idx];
        }
    }
    if(sz(str))
        res.pb(str);
    return res;
}


void solve()
{
    int ans = 0;
    cin>>n>>m;
    vector<vector<char>>grid(n,vector<char>(m));
    for(int i = 0; i<n; i++){
        for(int j = 0; j<m; j++){
            cin>>grid[i][j];
        }
    }
    vector<string>s = spirallyTraverse(grid);
    for(auto &str: s){
        int L = sz(str);
        for(int i = 0, j = 1%L, k = 2%L, l=3%L; i<L; i++){
            if(str[i]=='1' and str[j]=='5' and str[k]=='4' and str[l]=='3')
                ans++;
            j = (j+1)%L;
            k =  (k+1)%L;
            l = (l+1)%L;
        }
    }
    cout<<ans<<endl;
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
        // google(z);
        solve();
    }
}