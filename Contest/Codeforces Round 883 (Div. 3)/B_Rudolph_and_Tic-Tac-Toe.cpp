#include <bits/stdc++.h>
using namespace std;
 /********************************Macros********************************/
 #define mod 1000000007
#define pb push_back
#define fi first
#define se second
#define inf 0x3f3f3f3f
#define MAXN 100005
#define vi vector<int>
#define vll vector<long long>
#define set_bits(x) __builtin_popcount(x)
#define all(x) x.begin(), x.end()
#define rep(i, a, b) for (int i = (a); i < (b); ++i)
#define rev(i, a, b) for (int i = (a); i >= (b); --i)
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
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
 /****************************************************************/
 typedef long long ll;
typedef unsigned long long ull;
typedef long double lld;
 /********************************Debugger********************************/
 #ifndef ONLINE_JUDGE
#define debug(x) cerr << #x <<": "; _print(x); cerr << endl;
#else
#define debug(x)
#endif
 void _print(ll t) {cerr << t;}
void _print(int t) {cerr << t;}
void _print(string t) {cerr << t;}
void _print(char t) {cerr << t;}
void _print(lld t) {cerr << t;}
void _print(double t) {cerr << t;}
void _print(ull t) {cerr << t;}
 template <class T, class V> void _print(pair <T, V> p);
template <class T> void _print(vector <T> v);
template <class T> void _print(set <T> v);
template <class T, class V> void _print(map <T, V> v);
template <class T> void _print(multiset <T> v);
template <class T, class V> void _print(pair <T, V> p) {cerr << "{"; _print(p.ff); cerr << ","; _print(p.ss); cerr << "}";}
template <class T> void _print(vector <T> v) {cerr << "[ "; for (T i : v) {_print(i); cerr << " ";} cerr << "]";}
template <class T> void _print(set <T> v) {cerr << "[ "; for (T i : v) {_print(i); cerr << " ";} cerr << "]";}
template <class T> void _print(multiset <T> v) {cerr << "[ "; for (T i : v) {_print(i); cerr << " ";} cerr << "]";}
template <class T, class V> void _print(map <T, V> v) {cerr << "[ "; for (auto i : v) {_print(i); cerr << " ";} cerr << "]";}
 /****************************************************************/
 void solve()
{
    char arr[3][3];
    rep(i,0,3){
        rep(j,0,3){
            cin>>arr[i][j];
        }
    }
    rep(i, 0, 3)
    {
        if(arr[i][0]==arr[i][1]&&arr[i][1]==arr[i][2]&&arr[i][2]!='.'){
            cout<<arr[i][0]<<endl;
            return;
        }
        if (arr[0][i] == arr[1][i] && arr[1][i] == arr[2][i] && arr[2][i] != '.')
        {
            cout << arr[0][i] << endl;
            return;
        }
    }
    if (arr[0][0] == arr[1][1] && arr[1][1] == arr[2][2] && arr[2][2] != '.')
    {
        cout << arr[0][0] << endl;
        return;
    }
    if (arr[2][0] == arr[1][1] && arr[1][1] == arr[0][2] && arr[0][2] != '.')
    {
        cout << arr[2][0] << endl;
        return;
    }
    cout<<"DRAW"<<endl;
}
 int main()
{
    fastIO;
    int t;
    cin >> t;
    while (t--)
        solve();
}