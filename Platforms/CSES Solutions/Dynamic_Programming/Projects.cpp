#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
#define mod 998244353
#define inf 1e18+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define set_bits(x) __builtin_popcount(x)
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
vector<int>dp;
//dp[i] = maximum I can get from i to n
//dp[i] = max(dp[i+1], project[i].p + dp[next]) 
//start of next project should be greater than the end of project i(binary search)

struct Project{
    int s,e,p;
    void read(){
        cin>>s>>e>>p;
    }
    void write(){
        cout<<s<<' '<<e<<' '<<p<<endl;
    }
};

vector<Project>project;

int bs(int l, int r, int &val){
    if(l>r) return l;
    int mid = (l+r)/2;
    if(project[mid].s<=val) return bs(mid+1,r,val);
    return bs(l,mid-1,val);
}

int f(int pos){
    if(pos==n) return 0;
    if(dp[pos]!=-1) return dp[pos];
    int &ans = dp[pos];
    int next = bs(0,n-1,project[pos].e);
    ans = max({f(pos+1),project[pos].p+f(next)});
    return ans;
}


void solve()
{
    cin>>n;
    dp.resize(n,-1);
    project.resize(n);
    for(int i = 0; i<n; i++) project[i].read();
    sort(all(project),[](const Project &a, const Project &b){
        if(a.s==b.s) return a.e<b.e;
        return a.s<b.s;
    });
    cout<<f(0)<<endl;
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
        // google(z);
        solve();
    }
}