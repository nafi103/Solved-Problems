#include <bits/stdc++.h>
using namespace std;
 void solution(){
    int n,answer = 0;
    cin>>n;
    vector<int> v;
    for (int i = 0; i < n; i++)
    {
        int x;
        cin>>x;
        v.push_back(x);
        answer+= (x-1)/((2*v[0])-1);
    }
    cout<<answer<<endl;
}
 int main(){
    int t;
    cin>>t;
    while(t--)  solution();
}