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
int x[] = {-1,1,0,0};
int y[] = {0,0,1,-1};

bool valid(int i, int j){
    return i>=0 and i<n and j>=0 and j<m;
}


void solve()
{
    int one = 0;
    cin>>n>>m;
    vector<vector<int>>v(n,vector<int>(m));
    for(int i = 0; i<n; i++){
        readv(v[i]);
    }
    vector<bool>mark(n*m+1,false);
    set<int>s;
    for(int i = 0; i<n; i++){
        for(int j = 0; j<m; j++){
            if(mark[v[i][j]]) continue;
            s.insert(v[i][j]);
            for(int k = 0; k<4; k++){
                int nr = i+x[k], ny = j+y[k];
                if(valid(nr, ny) and v[i][j]==v[nr][ny]){
                    mark[v[i][j]] = true;
                    one++;
                    break;
                }
            }
        }
    }
    if(sz(s)==1){
        cout<<0<<endl;
        return;
    }
    if(!one) cout<<sz(s)-1<<endl;
    else{
        int not_one = sz(s) - one;
        one--;
        cout<<not_one+one*2<<endl;
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
        // google(z);
        solve();
    }
}