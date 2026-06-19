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

int dx[] = {1,0};
int dy[] = {0,1};

int bs(int l,  int r, int &k){
    if(l>r) return r;
    int mid = (l+r)/2;
    if((mid*(mid-1))/2 <= k) return bs(mid+1,r,k);
    else return bs(l,mid-1,k);
}

void solve()
{
    int k;
    cin>>k;
    using pii = pair<int,int>;
    vector<pii>ans;
    ans.reserve(500);
    ans.pb({0,0});
    int dir = 0;
    while(k>0){
        int x = bs(2,500,k);
        k-=(x*(x-1)/2);
        x--;
        while(x--){
            auto &[f,s] = ans.back(); 
            ans.pb({f+dx[dir],s+dy[dir]});
        }
        dir^=1;
    }
    cout<<sz(ans)<<endl;
    for(auto &[f,s]: ans){
        cout<<f<<" "<<s<<endl;
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
