// #include <bits/stdc++.h>
// using namespace std;

// /********************************Macros********************************/

// #define mod 1000000007
// #define pb push_back
// #define fi first
// #define se second
// #define inf 0x3f3f3f3f
// #define MAXN 100005
// #define ff first
// #define ss second
// #define set_bits(x) __builtin_popcount(x)
// #define all(x) x.begin(), x.end()
// #define rep(i, a, b) for (int i = (a); i < (b); ++i)
// #define rev(i, a, b) for (int i = (a); i >= (b); --i)
// #define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
// #define readv(v)      \
//     for (auto &x : v) \
//     cin >> x
// #define writev(v)     \
//     for (auto &x : v) \
//     cout << x << " "; \
//     cout<<endl
// #define endl "\n"
// #define yes cout<<"YES"<<endl
// #define no cout<<"NO"<<endl

// /****************************************************************/

// typedef unsigned int ui;
// typedef long long ll;
// typedef unsigned long long ull;
// typedef long double lld;
// typedef vector<int> vi;
// typedef vector<long long> vll;

// /********************************Debugger********************************/

// #ifndef ONLINE_JUDGE
// #define debug(x) cerr << #x <<": "; _print(x); cerr << endl;
// #else
// #define debug(x)
// #endif

// void _print(ll t) {cerr << t;}
// void _print(int t) {cerr << t;}
// void _print(string t) {cerr << t;}
// void _print(char t) {cerr << t;}
// void _print(lld t) {cerr << t;}
// void _print(double t) {cerr << t;}
// void _print(ull t) {cerr << t;}

// template <class T, class V> void _print(pair <T, V> p);
// template <class T> void _print(vector <T> v);
// template <class T> void _print(set <T> v);
// template <class T, class V> void _print(map <T, V> v);
// template <class T> void _print(multiset <T> v);
// template <class T, class V> void _print(pair <T, V> p) {cerr << "{"; _print(p.ff); cerr << ","; _print(p.ss); cerr << "}";}
// template <class T> void _print(vector <T> v) {cerr << "[ "; for (T i : v) {_print(i); cerr << " ";} cerr << "]";}
// template <class T> void _print(set <T> v) {cerr << "[ "; for (T i : v) {_print(i); cerr << " ";} cerr << "]";}
// template <class T> void _print(multiset <T> v) {cerr << "[ "; for (T i : v) {_print(i); cerr << " ";} cerr << "]";}
// template <class T, class V> void _print(map <T, V> v) {cerr << "[ "; for (auto i : v) {_print(i); cerr << " ";} cerr << "]";}

// /****************************************************************/

// bool place_possible(vi &stalls, int val, int &n, int &cows){
//     int cnt = 1, last = stalls[0], i = 0;
//     while(i<n){
//         i = lower_bound(stalls.begin()+i+1,stalls.end(),last+val)-stalls.begin();
//         if(i<n) {
//             cnt++;
//             last = stalls[i];
//         }
//     }
//     if(cnt>=cows)   return true;
//     return false;
// }

// int bs(int l, int h, vi &stalls,int &n,int &cows){
//     if(l>h) return h;
//     int mid = (l+h)/2;
//     if(place_possible(stalls,mid,n,cows))  return bs(mid+1,h,stalls,n,cows);
//     else return bs(l,mid-1,stalls,n,cows);
// }

// void solve()
// {
//     int n,c;
//     cin>>n>>c;
//     vi stalls(n);
//     readv(stalls);
//     sort(all(stalls));
//     cout<< bs(1,stalls[n-1]-stalls[0],stalls,n,c)<<endl;
// }

// int32_t main()
// {
//     fastIO;
// //  cout.precision(10);
// //  cout.setf(ios::fixed);
//     int t;
//     cin >> t;
//     while (t--)
//         solve();
// }




#include<bits/stdc++.h>
#define int long long
using namespace std;
const int mx = 100000 ;
int arr[mx];
int n, k;
bool ok(int pos){
    int cnt = 1;

    for(int i=1;i<n;i++){
        pos = 
    }
}
int32_t main()
{ 
    int tc;
    cin >> tc;

    while(tc--){
        cin >> n >> k;
        for(int i=0; i<n; i++) cin >> arr[i];
        sort(arr,arr+n);
        for(int i=0; i<n; i++) cout << arr[i] <<" ";

        int low = 0,high = *max_element(arr,arr+n);
        int ans = 0;
        for(int i =0 ;i<65;i++){
            int mid = (low+high)>>1;
            if()
        }
    }

    return 0;
}