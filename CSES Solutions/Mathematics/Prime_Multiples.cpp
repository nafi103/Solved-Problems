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

const double eps = 0;
vector<pair<int,int>>nums;
vector<int>primes;
int n,k;

void find_nums(int value, int pos, int taken){
    if(pos==k){
        if(value>1){
            nums.push_back({value,taken});
        }
        return;
    }
    if(log2(n)-log2(value)-log2(primes[pos])>=eps)
        find_nums(value*primes[pos],pos+1,taken+1);
    find_nums(value,pos+1,taken);
}


void solve()
{
    cin>>n>>k;
    primes.resize(k);
    readv(primes);
    find_nums(1,0,0);
    int ans = 0;
    for(auto &[f,s]: nums){
        if(f<=1)
            continue;
        if(s&1){
            ans+=(n/f);
        }else{
            ans-=(n/f);
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
    nums.reserve(2e6);
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}